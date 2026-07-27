# CHALLENGE-R3.proposed.md — justification for the proposed R3 headlines

Status: **PENDING HUMAN REVIEW** (R3 charter hard gate). The live
Challenge.lean R3 section is untouched. The proposed statements compile:
`lake env lean OV/CHALLENGE-R3.proposed.lean` succeeds with exactly the
two `declaration uses 'sorry'` warnings (the correct final state for this
tier), and `lake build OV` / `lake build Challenge` remain green.

## 1. Verdict on the FREEZE-0 `ov_license` draft: REPLACE (both halves)

FREEZE-0 stated, for ANY ring `B` and any `M : ℕ → B`:
`(HasFiniteOVHankelRank ↔ HasFiniteRealization) ∧ (HasFiniteRealization ↔
IsFinitelyAtomicOV)` — with the Hankel rank defined as "the left span of the
shifts of `M` is a finitely generated module", and atomicity as
`M n = ∑ i, w i * (a i) ^ n` with unconstrained `w, a ∈ B`.

### 1a. First iff (rank ⟺ rational): FIX the rank definition (Noetherian gap)

* Direction "f.g. shift span ⇒ realization" is fine: the span of shifts is
  shift-stable and contains `M`; picking generators `g₁ … g_N`, writing
  `shift g_j = ∑ l A j l • g_l` and `M = ∑ j b j • g_j` yields
  `M n = b ⬝ᵥ ((A ^ n) *ᵥ (fun l => g_l 0))` by induction (matrix order works
  out for LEFT modules with left coefficients).
* Direction "realization ⇒ f.g. shift span" has NO license over a general
  ring. From `M n = c ⬝ᵥ ((A ^ n) *ᵥ b)` and `A^(n+k) = A^k * A^n`, the
  `k`-th shift is `(c ᵥ* A^k) ⬝ᵥ ((A ^ n) *ᵥ b)`: the shifts lie in the f.g.
  shift-stable left module spanned by `h_j : n ↦ ((A ^ n) *ᵥ b) j`. That
  makes the SPAN of the shifts a SUBMODULE of a f.g. module — finitely
  generated only when `B` is left-Noetherian. MSY's `B` (a von Neumann
  algebra) is not Noetherian, so FREEZE-0's definition is not even the right
  notion for the motivating case.
* Fix adopted: `HasFiniteOVHankelRankStable` (OV/Vocab.lean) — "`M` lies
  in a finitely generated shift-stable left submodule". This is Fliess's
  stable-submodule characterization of recognizable series (Fliess 1974;
  Berstel–Reutenauer Ch. 2), it coincides with FREEZE-0's notion for
  left-Noetherian `B` (in particular for fields, recovering R0/Kronecker),
  and with it "rank ⟺ rational" is theorem-shaped over EVERY ring — both
  directions sketched above. No star, order, or moment hypothesis is needed
  for this half.

### 1b. Second iff (rational ⟺ atomic): FALSE as frozen; positivity restores it

The unconditional claim "realization ⇒ atomic" fails already over fields:

* `B = ℝ`, `M n = cos (n θ)` for generic `θ`: realized by a 2×2 rotation
  matrix, but `cos (n θ) = ∑ i w i * a i ^ n` with finitely many REAL
  `a i` is impossible (it needs the complex atoms `e^{±iθ}`).
* `B = ℂ`, `M n = n λ ^ n` (a 2×2 Jordan block realization): rational, but a
  plain exponential sum `∑ w i * a i ^ n` cannot produce the polynomial
  factor `n` — this is why R0's scalar statement needs exponential-POLYNOMIAL
  atoms plus `IsAlgClosed`/`CharZero`, none of which FREEZE-0 carried.

So the honest MSY shape must add star/positivity structure — and positivity
is exactly what kills both counterexamples: the Hankel kernels
`(cos ((i+j) θ))` and `((i+j) λ^{i+j})` are not positive semidefinite. The
proposal therefore:

* assumes `[StarRing B] [PartialOrder B] [StarOrderedRing B]` and the moment
  hypothesis `hM : IsOVMomentSequence B M` (hermitian entries + PSD
  `B`-valued Hankel kernel — the algebraic shadow of "`M n = E_B (xⁿ)`, `x`
  self-adjoint, `E_B` positive"), and
* replaces atomicity by `IsFinitelyAtomicOVStar`:
  `M n = ∑ i, star (w i) * (a i) ^ n * w i` with SELF-ADJOINT atoms
  `a i ∈ B` and sandwich-positive weights.

Soundness checks done on the new shape (⇐ direction, valid over every
star-ordered ring, by direct computation):

* atomic-star ⇒ realization: diagonal `A = diag (a i)`, `c = star ∘ w`,
  `b = w`;
* atomic-star ⇒ PSD Hankel:
  `∑ i j, star (b i) * M (i+j) * b j = ∑ l star (v l) * v l ≥ 0` with
  `v l = ∑ i (a l) ^ i * (w l * b i)` (uses `star (a l) = a l`);
* atomic-star ⇒ hermitian entries: `star` reverses the sandwich onto itself.

Status of the ⇒ direction (the frontier claim, `sorry` by design):

* `B = ℂ`: classical (Hamburger + Kronecker: a PSD Hankel of finite rank is
  the moment matrix of a finitely atomic positive measure on ℝ — real atoms,
  weights `|w|² = star w * w`). The proposal degenerates to a true theorem.
* `B = Mₚ(ℂ)`: matrix Hamburger moment problem — still true (finitely atomic
  matrix measure, `a i` scalar matrices `t i • 1`, `w i = W i ^ (1/2)`).
* Atoms must be allowed IN `B`, not just scalars — FREEZE-0's instinct here
  was right and is kept. Witness: `B = A = L^∞[0,1]`, `E = id`,
  `M n = tⁿ`: the scalarized spectral measure is diffuse, yet the `B`-Hankel
  rank is 1 and `M` IS atomic in the `B`-valued sense (single atom `a = t`,
  the `B`-valued Dirac `δ_t`). Any "scalar-atoms" version of the headline
  would be falsified by this example; the atoms-in-`B` version is exactly
  what makes it MSY-shaped (atomic `E_B`-conditioned distribution).
* General star-ordered `B`: genuinely open/frontier. KNOWN RISKS for the
  reviewer: (i) without functional calculus (square roots, spectral
  projections in `B`) the atomic decomposition may need `B` to be a
  C*-algebra — an optional strengthening is `[CStarAlgebra B]` with the
  order instance; (ii) level-1 PSD may be too weak — the analytic setting
  gives COMPLETE positivity; strengthening `OVHankelPSD` to all matrix
  amplifications is a reviewer option; (iii) atoms might honestly live in a
  matrix amplification `Mₙ(B)` with `M` a compressed corner. We propose the
  minimal form and flag; any of (i)–(iii) can be imposed without changing
  the architecture.

## 2. `ov_completeness`: design and plausibility

FREEZE-0 had `True := sorry` (placeholder). The proposal is the first real
statement. Shape (per the free-Ax–Schanuel line: every genuine alignment has
a structural cause):

* Data: a self-adjoint tuple `x : Fin d → A` in a complex star algebra,
  conditioned by `E : A →ₗ[ℂ] B`.
* *Alignment at level `n`* (`HasOVAlignment`): a nonzero `c : words →₀ ℂ`
  supported in length ≤ `n` with
  `∑_w c_w E (x_{w w'}) = 0` for EVERY word `w'` — i.e. the rows of the
  word-indexed `B`-valued moment/Hankel kernel are dependent, so its rank
  drops below the generic (free) value `#{words of length ≤ n}`.
* *Structural cause* (`HasPolyCause`): a nonzero `p ∈ FreeAlgebra ℂ (Fin d)`
  in the span of monomials of length ≤ `n` (nonzero is meaningful via
  `FreeAlgebra.basisFreeMonoid`) with `FreeAlgebra.lift ℂ x p = 0` — an
  exact noncommutative algebraic relation, with the degree bound making the
  cause LOCAL to the level of the alignment.
* *Genericity/freeness parameter*: `hfaith : E (star a * a) = 0 → a = 0`
  (faithfulness on positives), plus `hsa` (self-adjoint tuple). This is the
  abstract role of the faithful normal conditional expectation / trace in
  the free-probability regularity line (Mai–Speicher–Weber). It is stated as
  an explicit hypothesis, as directed, so the reviewer can see exactly what
  "genuine" costs.

Why this is true-shaped and not vacuous: from the alignment,
`E (y * x_{w'}) = 0` for all words `w'`, where `y = ∑_w c_w x_w`. Since the
`x i` are self-adjoint, `star y` is again a word combination, so linearity
gives `E (y * star y) = E (star (star y) * star y) = 0`; faithfulness forces
`star y = 0`, hence `y = 0`, and `p = ∑_w c_w ·(monomial w)` is the nonzero
annihilating polynomial of degree ≤ `n`. Note the alignment hypothesis only
sees MOMENT data (no stars, one-sided rows); faithfulness + self-adjointness
is precisely what converts moment-level degeneracy into an exact relation —
without `hfaith` the statement is false (take `E = 0`: every tuple aligns,
free tuples have no cause).

Deliberately NOT claimed (and why): the converse (cause ⇒ alignment) is
trivially true and adds nothing; a `B`-coefficient version of the alignment
(the honest amalgamated form) needs the `B`-bimodule Hankel and free
products with amalgamation — out of minimal scope, flagged below.

## 3. Consolidated simplification flags

| # | Simplification | Where | Honest cost |
|---|---|---|---|
| 1 | left `B`-modules, not `B`-bimodules | `IsShiftStable`, `HasFiniteOVHankelRankStable` | the amalgamated (bimodule) Hankel of MSY is not modelled |
| 2 | one variable (`ℕ`-indexed) for the license; words only in `ov_completeness` | Defs/Vocab | multivariate OV license not stated |
| 3 | level-1 positivity, not complete positivity | `OVHankelPSD` | may be strictly weaker over noncommutative `B`; reviewer option to strengthen |
| 4 | `B` abstract star-ordered ring, not a von Neumann algebra; no normality/continuity | `ov_license` | frontier direction may need C*/W* structure |
| 5 | atoms in `B`, weights `star w * w`; no commutation/`M 0`-mass constraints | `IsFinitelyAtomicOVStar` | coarser than "atomic `B`-valued spectral measure" |
| 6 | `E` a bare ℂ-linear map; bimodularity, unitality, complete positivity dropped; faithfulness reinstated as hypothesis | `HasOVAlignment`, `ov_completeness` | `E_B` is not constructed (Mathlib has only measure-theoretic `condExp`; see VOCAB.md) |
| 7 | scalar (ℂ) alignment coefficients, not `B`-valued | `HasOVAlignment` | the full amalgamated alignment notion is stronger |
| 8 | no exponential-polynomial (multiplicity) layer in atomicity | `IsFinitelyAtomicOVStar` | intentionally excluded — positivity is exactly the hypothesis that kills Jordan blocks; if review weakens positivity, multiplicities must return |

## 3b. STEERING-02 — the operator lift of the conditioning tier, and the
## COLLAPSE VERDICT

Deliverables of this round: `OV/Cond.lean` (definitions + all collapse
tests, **proved, zero `sorry`**) and three proposed headlines in
`CHALLENGE-R3.proposed.lean` (`ov_condition_number_theorem`,
`ov_cnt_recovers_scalar`, `ov_dist_not_element_valued`).

### 3b.1 The definition of `dist_B(x, Σ)`

Setting (finite-dimensional, exact, no analysis): `B` a star-ordered ring,
`A = Mₙ(B)`, ill-posed set `Σ = {y : ¬ IsUnit y}` (`R3.IsIllPosed`), and the
Hilbert-C*-module forms on `Bⁿ` written algebraically:
`⟨ξ, η⟩ = ∑ᵢ ξᵢ* ηᵢ` (`R3.ovInner`) and `⟨ξ, b ξ⟩ = ∑ᵢ ξᵢ* b ξᵢ`
(`R3.ovRayleigh`). Then

* `R3.IsMargin x b` := `0 ≤ b ∧ ∀ ξ, ⟨ξ, b ξ⟩ ≤ ⟨xξ, xξ⟩` — "`b` is a
  certified `B`-valued margin", the operator-valued `σ_min(x)² ≥ b`;
* **`R3.distB x := {b | IsMargin x b}` is `dist_B(x, Σ)`** — the `B`-valued
  distance object, a certificate SET, downward closed in the positive cone;
* `R3.IsBValuedDistance x b := IsGreatest (distB x) b` — "`b` IS the
  `B`-valued distance", when a greatest margin exists;
* `R3.IsDistanceCertificate x b` — the geometric side: every `y ∈ Σ` is at
  least `b` away from `x`, measured on `ker y`.

Citation for the shape: Demmel 1987 (`κ = ‖x‖/dist(x,Σ)`);
Bürgisser–Cucker 2013; Eckart–Young 1936 for the rank-one construction;
Paschke/Lance for the Hilbert-module inner product; Kadison 1951 for the
anti-lattice obstruction below; Watatani 1990 as the nearest algebra-valued
neighbour (SWEEP S2).

That `dist_B` is a SET and not an element of `B` is **forced**, not a
stylistic dodge — see 3b.3.

### 3b.2 Collapse test 1 (naive definition D1): PROVEN COLLAPSE — D1 IS DEAD

The first definition anyone writes is a global infimum over `Σ` of the
conditioned squared perturbation,
`dist_B(x,Σ)² "=" inf { E_B(δ*δ) : x - δ ∈ Σ }` (`R3.IsGlobalInfMargin`).

`R3.globalInf_collapses` **proves it is identically `0`**, in the most
favourable possible instance: `B = ℝ × ℝ` (commutative — so infima are not
obstructed), `A = B`, `E = id` (the conditional expectation loses NO
information), and `x = (1,2)` invertible with scalar condition number 2. The
two ill-posed points `(0,2)` and `(1,0)` give `E(δ*δ) = (1,0)` and `(0,4)`,
whose only common positive lower bound is `0`.

Reading: `Σ` is cheap in *every* direction of `B`, so any global infimum is
zero. A `B`-valued distance must be **compressed** to the corner of `B` where
the ill-posed direction lives — which is exactly why the surviving
formulation quantifies over kernels of individual `y ∈ Σ`. This is a
first-class negative and it is reported as one.

### 3b.3 The structural theorem: `dist_B` CANNOT be an element of `B`

`R3.isMargin_diagonal_iff` (proved) computes the whole margin set of a
diagonal matrix:

> `IsMargin (diagonal d) b ↔ 0 ≤ b ∧ ∀ i, b ≤ (dᵢ)* dᵢ`

i.e. the operator-valued `σ_min(diag d)² = minᵢ |dᵢ|²`, with `min` replaced by
"common lower bound". Hence (`R3.infima_of_bvaluedDistance_diagonal`, proved):

> if every `2 × 2` diagonal matrix over `B` has a `B`-VALUED distance, then
> every pair of positive elements `d₁*d₁, d₂*d₂` has a greatest common lower
> bound in `B₊`,

and contrapositively (`R3.bvaluedDistance_fails_of_no_infimum`, proved): if
`B₊` is not an inf-semilattice then some `x ∈ M₂(B)` has **no** `B`-valued
distance at all.

By **Kadison's anti-lattice theorem** (Proc. AMS 2 (1951) 505–510) the
self-adjoint part of a factor is an anti-lattice, and the same failure occurs
in the positive cone. Hand-verified witness in `B = M₂(ℝ)` (rational
arithmetic, exact):

* `a₁ = diag(2,1)`, `a₂ = [[3/2,1/2],[1/2,3/2]]` (both positive, incomparable);
* `1` is a common lower bound: `a₁ - 1 = diag(1,0) ⪰ 0`,
  `a₂ - 1 = ½[[1,1],[1,1]] ⪰ 0`;
* `c = diag(21/20, 9/10)` is another: `a₁ - c = diag(19/20, 1/10) ⪰ 0`, and
  `a₂ - c = [[9/20,1/2],[1/2,3/5]]` has trace `> 0` and determinant
  `27/100 - 25/100 = 1/50 > 0`, hence `⪰ 0`;
* `1` and `c` are incomparable (`1 - c = diag(-1/20, 1/10)`);
* no greatest common lower bound exists: a greatest `m` would satisfy
  `m ⪰ 1` and `m ⪯ a₁`, forcing `m₂₂ = 1`, hence (zero diagonal entry of the
  positive `a₁ - m`) `m₁₂ = 0`; then `m ⪯ a₂` forces
  `(3/2 - m₁₁)(1/2) ≥ 1/4`, i.e. `m₁₁ ≤ 1`, contradicting `m ⪰ c`
  (`m₁₁ ≥ 21/20`).

The general reduction is machine-checked; this instance is stated as the
TARGET `ov_dist_not_element_valued` and is currently hand-verified only —
flagged as such, not claimed as proved.

**Consequence, stated plainly: the operator-valued condition number is not a
number in `B`. It is a set of certificates.** Every downstream statement must
be certificate-shaped (`IsMargin` / `IsDistanceCertificate`), and the phrase
"the condition number is an element of `B`" — the framing this tier started
from — is FALSE for the noncommutative `B` the tier exists to serve.

### 3b.4 Collapse test 2 (the surviving object): verdict

Named failure mode: *if `dist_B` collapses to `λ_min` or to a norm, the
definition is a renaming and the tier is dead.*

* **Not `λ_min`, not a norm, not any scalar invariant** —
  `R3.bvaluedDistance_not_scalar` (proved): `witnessX = (1,2)` and
  `witnessX' = (2,1)` over `B = ℝ × ℝ` have identical scalar condition data
  (`‖x‖ = 2`, `σ_min = 1`, `κ = 2`) but `B`-valued distances `(1,4)` and
  `(4,1)`; the best scalar margin for either is `t ≤ 1 = λ_min`, strictly
  below the `B`-valued answer in one fibre. So the object strictly refines
  `λ_min` and is not a function of any scalar invariant. **Test 2 passed.**
* **But the SWEEP-S2 collapse condition FIRES in the abelian case.** For
  abelian `B` (equivalently: `E_B` onto a masa, `B ≅ C(X)`), `isMargin_diagonal_iff`
  says the margin set is the fibrewise `{b(ω) ≤ σ_min(x(ω))²}` — i.e.
  `dist_B` is exactly a **componentwise condition number**, and the
  componentwise/structured literature (Skeel; Rohn; Higham; the corpus
  catalogued in `Conditioning/SWEEP.md` S2) is mature and occupied. In the
  abelian case this tier has **no novelty**, and says so.
* Combined with 3b.3 this is a **dichotomy**:
  - `B` abelian ⇒ `B₊` is a lattice ⇒ `dist_B` exists as an element and IS
    the already-published componentwise condition number (collapse into
    known art);
  - `B` noncommutative (factor) ⇒ `dist_B` is **not** element-valued at all;
    what survives is the certificate set, which no existing literature
    formulates.

**Overall verdict: the tier is NOT dead, but its claim is now much narrower
and much sharper than "the condition number is an element of `B`".** The
surviving, defensible claim is: *the operator-valued conditioning object is a
certificate set; it is element-valued exactly in the abelian case, where it
reduces to known componentwise conditioning; the noncommutative content is
the anti-lattice obstruction itself.* An operator who wants a `B`-valued
NUMBER should read 3b.3 as a refutation and retire that framing.

### 3b.5 What is genuinely new vs. what is bookkeeping (honest split)

* Genuinely new: the certificate-set formulation; the diagonal reduction
  identifying the margin set with common lower bounds; the anti-lattice
  obstruction as a theorem about conditioning; the proved death of the naive
  global-infimum definition.
* Bookkeeping (the scalar argument verbatim): `margin_imp_distanceCertificate`
  and `margin_imp_inverse_bound` — both proved, both easy. The `⇐` half of
  `ov_condition_number_theorem` is the Eckart–Young rank-one construction and
  is expected to be equally routine. **The mathematical weight of the
  `B`-valued CNT is in the definition, not in the argument** — which is
  precisely why the collapse tests, not the proofs, decide this tier.

### 3b.6 Simplification flags for the conditioning layer

| # | Simplification | Where |
|---|---|---|
| C1 | `B` an abstract star-ordered ring; no norm, no completeness, no C*-identity | all of `Cond.lean` |
| C2 | `Σ` = non-units of `Mₙ(B)`; no rank-`k` stratification of the ill-posed set | `IsIllPosed` |
| C3 | margins over all `ξ`, unit vectors (`⟨ξ,ξ⟩ = 1`) only in the headline; kernel projections (`⟨ξ,ξ⟩ = p`) not modelled | `IsMargin`, `ov_condition_number_theorem` |
| C4 | no `E_B` appears: with `A = Mₙ(B)` the conditioning is carried by the module structure, so the promised "distance measured in `E_B`" is realized as the `B`-valued inner product, not as a Tomiyama projection | `ovInner` |
| C5 | κ itself is never formed (it would be `‖x‖·b⁻¹`-shaped and needs `b` invertible); only margins and certificates | `margin_imp_inverse_bound` |

## 4. Merge mechanics (for the orchestrator, post-approval)

1. Move/keep `OV/Vocab.lean` definitions in the R3 definitional layer
   (they extend, and do not alter, FREEZE-0 `Defs.lean`).
2. Replace the two R3 statements in Challenge.lean by the two theorems in
   `CHALLENGE-R3.proposed.lean` verbatim (drop the `ProposedR3` namespace).
3. Dated changelog entry in STATEMENTS.md (R3 rows): `ov_license` — rank
   definition corrected (Fliess stable form), positivity hypotheses added,
   atomicity star-corrected, with the FREEZE-0 unconditional iff recorded as
   retracted-as-false; `ov_completeness` — placeholder `True` replaced by
   the alignment ⇒ cause implication.
4. `CHALLENGE-R3.proposed.lean` builds as module
   `OV.«CHALLENGE-R3.proposed»` under the existing `OV.+` glob (green,
   two sorry warnings); after merge it can be deleted or kept as record.
