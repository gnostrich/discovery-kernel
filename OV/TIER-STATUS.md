# TIER-STATUS — R3 — operator lift of the conditioning tier

Reframed by STEERING-02 (2026-07-27): R3 is the OPERATOR LIFT of
`Conditioning/`. Sorries are now labelled TARGET (intended to be proven) or
DECLARED-OPEN (frontier, no proof claimed).

## Proven (no `sorry`, in `OV/Cond.lean`)

* `globalInf_collapses` — the naive global-infimum `dist_B` is identically
  `0` (collapse test 1: NEGATIVE, definition D1 dead).
* `bvaluedDistance_not_scalar` — `dist_B` is not `λ_min`, not a norm, not any
  scalar invariant (collapse test 2: passed, weakly — see the abelian caveat).
* `isMargin_diagonal_iff`, `distB_diagonal` — the margin set of a diagonal
  matrix = positive common lower bounds of `(dᵢ)* dᵢ`.
* `infima_of_bvaluedDistance_diagonal`, `bvaluedDistance_fails_of_no_infimum`
  — the anti-lattice obstruction: `dist_B` is element-valued only if `B₊` is
  an inf-semilattice; otherwise no `B`-valued distance exists at all.
* `margin_imp_distanceCertificate`, `margin_imp_inverse_bound` — the easy
  (scalar-verbatim) halves of the `B`-valued Condition Number Theorem.

Symbolic (fallback) form, in `OV/Symbolic.lean` — also no `sorry`:

* `ovVanishingOrder` and the per-direction layer (`ovFamilyImage`,
  `ovDatumCoeff`, `ovLeadingCertificate`, `IsDegenerateAtZero`).
* `exponentTuple_not_constant` — abelian witness: orders `1` and `2` in two
  directions of the family `t ↦ (t, t²)` over `ℝ × ℝ`.
* `exponentTuple_not_constant_noncomm` — NONCOMMUTATIVE witness: orders `1`
  and `2` for `t ↦ e₁t + e₂t²` over `M₂(ℝ)`.

## Sorry ledger (every sorry labelled)

| Statement | File | Label |
|---|---|---|
| `ov_license` (MSY iff-chain, positivity-corrected) | `CHALLENGE-R3.proposed.lean` | DECLARED-OPEN (frontier; true for `B = ℂ`, `Mₚ(ℂ)`) |
| `ov_completeness` (alignment ⇒ structural cause) | `CHALLENGE-R3.proposed.lean` | TARGET (proof sketch in the .md: faithfulness + self-adjointness) |
| `ov_condition_number_theorem` (`B`-valued CNT) | `CHALLENGE-R3.proposed.lean` | TARGET (`⇒` already proved; `⇐` = Eckart–Young rank-one) |
| `ov_cnt_recovers_scalar` (`B = ℝ` ⇒ `λ_min`) | `CHALLENGE-R3.proposed.lean` | TARGET (needs Courant–Fischer, absent from Mathlib — SWEEP S1) |
| `ov_dist_not_element_valued` (Kadison witness in `M₂(ℝ)`) | `CHALLENGE-R3.proposed.lean` | TARGET (hand-verified exact rational arithmetic in the .md; the reduction it rests on is already proved) |
| `ov_lojasiewicz_order` (symbolic FALLBACK form) | `CHALLENGE-R3.proposed.lean` | TARGET (order-of-vanishing bookkeeping + faithfulness of the positive cone) |
| Challenge.lean R3 entries (FREEZE-0 text) | `Challenge.lean` | untouched; superseded by the proposals below |

## COLLAPSE VERDICT (first-class result, stated plainly)

1. The naive `dist_B` (global infimum over `Σ` of `E_B(δ*δ)`) **collapses to
   zero** — PROVED, even with `E = id`, commutative `B`, and a
   well-conditioned `x`. That definition is dead; the bound must be
   compressed to the kernel of each ill-posed `y`.
2. The surviving object does **not** collapse to `λ_min` or to a norm —
   PROVED by a witness pair with identical scalar condition data and
   different `B`-valued distances.
3. **But the operator-valued condition number is NOT an element of `B`.** By
   the proved diagonal reduction plus Kadison's anti-lattice theorem, a
   greatest certified margin fails to exist over a factor. `dist_B` is a
   CERTIFICATE SET. The framing "the condition number is an element of `B`"
   is refuted for exactly the noncommutative algebras this tier exists for.
4. **Abelian collapse (the SWEEP S2 condition) FIRES**: for abelian `B` the
   object is precisely a componentwise condition number — mature, occupied
   literature (Skeel; Rohn; Higham). No novelty there.
5. Net: the tier survives, narrowly, with a sharper claim — the conditioning
   object is certificate-shaped; element-valued exactly in the abelian
   (already-published) case; the noncommutative content is the obstruction
   itself. Full argument, witnesses and hand-verified arithmetic:
   `OV/CHALLENGE-R3.proposed.md` §3b.

## COLLAPSE VERDICT — SYMBOLIC (fallback) form, STEERING-02a

**NO COLLAPSE — the symbolic form survives, and unlike the metric form it
survives in the noncommutative setting.** The test (identical to the
occupancy test per `OV/SWEEP.md` S3: a constant exponent tuple would be both
vacuous and the published single-exponent object) demanded a witness with two
directions of different vanishing order. Two are proved:

* `exponentTuple_not_constant` — `B = ℝ × ℝ`, family `t ↦ (t, t²)`, orders
  `1` and `2` (abelian);
* `exponentTuple_not_constant_noncomm` — `B = M₂(ℝ)`, family
  `t ↦ e₁t + e₂t²`, orders `1` and `2` (noncommutative — the case the sweep
  found unoccupied).

No novelty is claimed for Łojasiewicz-with-explicit-exponents on `σ_min` of
real polynomial matrices (arXiv 1604.02805, including the distance-function
versions); the claims are exactly the two properties S3 found missing: the
algebra-valued setting and the per-direction tuple.

**Boundary held:** both forms need a parametrised family; a single
`x ∈ Mₙ(B)` has none, and none was invented. Symbolic proof search over a
proof library remains CLOSED.

## Delivered files

`VOCAB.md` (Mathlib survey), `Vocab.lean` (OV definitional layer),
`Cond.lean` (metric conditioning layer, all proofs complete),
`Symbolic.lean` (symbolic/Łojasiewicz layer, all proofs complete),
`CHALLENGE-R3.proposed.{lean,md}`. `lake build OV` and
`lake build Challenge` green; `Challenge.lean` untouched.

## PENDING HUMAN REVIEW

All six statements below are PROPOSALS (R3 charter hard gate); the
orchestrator holds the merge until the operator approves. Justification,
counterexamples and the collapse verdict: `CHALLENGE-R3.proposed.md`;
definitions: `OV/Vocab.lean`, `OV/Cond.lean` (both extend, and do not
alter, FREEZE-0 `Defs.lean`).

### Proposed `ov_license` (MSY-shaped; replaces the FREEZE-0 draft, which is FALSE)

```lean
theorem ov_license
    {B : Type} [Ring B] [StarRing B] [PartialOrder B] [StarOrderedRing B]
    (M : ℕ → B) (hM : R3.IsOVMomentSequence B M) :
    (R3.HasFiniteOVHankelRankStable B M ↔ R3.HasFiniteRealization B M) ∧
      (R3.HasFiniteRealization B M ↔ R3.IsFinitelyAtomicOVStar B M) := sorry
```

### Proposed `ov_completeness` (free-Ax–Schanuel-shaped; replaces `True`)

```lean
theorem ov_completeness
    {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]
    {B : Type} [AddCommGroup B] [Module ℂ B]
    (E : A →ₗ[ℂ] B) {d : ℕ} (x : Fin d → A) (n : ℕ)
    (hsa : ∀ i, star (x i) = x i)
    (hfaith : ∀ a : A, E (star a * a) = 0 → a = 0)
    (halign : R3.HasOVAlignment E x n) :
    R3.HasPolyCause x n := sorry
```

### Proposed `ov_condition_number_theorem` (STEERING-02 operator lift)

```lean
theorem ov_condition_number_theorem
    {B : Type} [Ring B] [StarRing B] [PartialOrder B] [StarOrderedRing B]
    {n : ℕ} (x : Matrix (Fin n) (Fin n) B) (b : B) (hb : 0 ≤ b) :
    (∀ ξ : Fin n → B, R3.ovInner B ξ ξ = 1 →
        R3.ovRayleigh B b ξ ≤ R3.ovInner B (x *ᵥ ξ) (x *ᵥ ξ)) ↔
      (∀ y : Matrix (Fin n) (Fin n) B, R3.IsIllPosed B y → ∀ ξ : Fin n → B,
        R3.ovInner B ξ ξ = 1 → y *ᵥ ξ = 0 →
          R3.ovRayleigh B b ξ ≤ R3.ovInner B ((x - y) *ᵥ ξ) ((x - y) *ᵥ ξ)) := sorry
```

### Proposed `ov_cnt_recovers_scalar` (obligatory scalar base case)

```lean
theorem ov_cnt_recovers_scalar
    {n : ℕ} (x : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    R3.IsMargin ℝ x t ↔
      0 ≤ t ∧ ∀ i, t ≤ (Matrix.isHermitian_conjTranspose_mul_self x).eigenvalues i := sorry
```

### Proposed `ov_dist_not_element_valued` (the decisive negative)

```lean
open scoped MatrixOrder in
theorem ov_dist_not_element_valued :
    ∃ x : Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) ℝ),
      ∀ b : Matrix (Fin 2) (Fin 2) ℝ,
        ¬ R3.IsBValuedDistance (Matrix (Fin 2) (Fin 2) ℝ) x b := sorry
```

### Proposed `ov_lojasiewicz_order` (symbolic FALLBACK form, STEERING-02a)

```lean
theorem ov_lojasiewicz_order
    {B : Type} [Ring B] [StarRing B] [PartialOrder B] [StarOrderedRing B]
    (hfaith : ∀ c : B, star c * c = 0 → c = 0)
    {n : ℕ} (X : Matrix (Fin n) (Fin n) (Polynomial B))
    (hdeg : R3.IsDegenerateAtZero B X)
    (ξ : Fin n → B) (k : ℕ)
    (hk : R3.ovVanishingOrder B X ξ = (k : ℕ∞)) :
    (∀ j < k, R3.ovDatumCoeff B X ξ j = 0) ∧
      0 < R3.ovLeadingCertificate B X ξ k := sorry
```

PRIMARY = the metric statements above; FALLBACK = this one. The marking is
also carried in the proposal file's section headers.

Reviewer decision points: (1) complete vs level-1 positivity in
`OVHankelPSD`; (2) restrict `B` to a C*-algebra in `ov_license`'s second
chain; (3) atoms in matrix amplifications `Mₙ(B)`; (4) scalar vs `B`-valued
alignment coefficients; (5) **whether the tier keeps the certificate-set
framing, given that the element-valued framing is refuted (§3b.3)**;
(6) whether the symbolic fallback is promoted alongside the metric primary,
given that it is the only one of the two whose surviving content is
noncommutative.
