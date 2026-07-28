# TIER-STATUS — R3 — operator lift of the conditioning tier

Reframed by STEERING-02 (2026-07-27): R3 is the OPERATOR LIFT of
`Conditioning/`. Sorries are labelled TARGET (intended to be proven) or
DECLARED-OPEN (frontier, no proof claimed).

**2026-07-28 — statements SIGNED OFF by the operator and live in
`Challenge.lean`. Proof phase run. Headline status now:**

| Challenge headline | Status | Solution constant (`OV/Proofs.lean`) |
|---|---|---|
| `ov_dist_not_element_valued` | **PROVEN** | `DiscoveryKernels.R3.ov_dist_not_element_valued` |
| `ov_condition_number_theorem` | **PROVEN** | `DiscoveryKernels.R3.ov_condition_number_theorem` |
| `ov_cnt_recovers_scalar` | **PROVEN** | `DiscoveryKernels.R3.ov_cnt_recovers_scalar` |
| `ov_lojasiewicz_order` | **PROVEN** | `DiscoveryKernels.R3.ov_lojasiewicz_order` |
| `ov_completeness` | **TARGET-still-open** (1 labelled `sorry`) | `DiscoveryKernels.R3.ov_completeness` (conditional forms proven: `…_of_star_scalars`, `…_of_starModule`) |
| `ov_license` | **DECLARED-OPEN** (MSY frontier; not attempted) | — |

All four proven solutions were checked with the comparator's own `isDefEq`
test against the frozen `Challenge.lean` statements (5/5 statement matches,
including the still-open `ov_completeness`) and with `#print axioms`: every
one is `[propext, Classical.choice, Quot.sound]`. No `native_decide`, no
`Float`, no allowlist extension requested. Comparator rows to apply:
`OV/COMPARATOR-ROWS.md`.

### The one open target, stated precisely

`ov_completeness` is proved except for a single missing input, and the gap is
a STATEMENT-level omission, not a proof failure:

* `DiscoveryKernels.R3.ov_completeness_of_star_scalars` — the entire argument,
  `sorry`-free, under the extra hypothesis
  `hscal : ∀ z : ℂ, ∃ z', star (algebraMap ℂ A z) = algebraMap ℂ A z'`.
* `DiscoveryKernels.R3.ov_completeness_of_starModule` — the same, `sorry`-free,
  under `[StarModule ℂ A]` (which supplies `hscal`). This is the intended
  setting: `A` an honest `*`-algebra over `ℂ` (Mai–Speicher–Weber).
* The frozen statement assumes only `[Ring A] [StarRing A] [Algebra ℂ A]`,
  which does NOT imply `hscal` — and that is itself now MACHINE-CHECKED:
  `DiscoveryKernels.R3.star_algebraMap_not_in_range` (no `sorry`) exhibits
  `TwistCC = ℂ × ℂ` with `algebraMap z = (z,z)` and `star (s,t) = (s, conj t)`,
  a lawful `StarRing` + `Algebra ℂ` pair with
  `star (algebraMap ℂ A I) = (I, -I) ∉ Set.range (algebraMap ℂ A)`.
  Without `hscal` the ℂ-span `W` of the words `x_w` is not `star`-stable, so
  `star a` (for `a` the alignment combination) need not lie in `W` and the
  faithfulness hypothesis cannot be applied to it.
* HONEST CAVEAT: this shows the natural route is blocked, NOT that the
  headline is false — no counterexample to `ov_completeness` itself was found
  (faithfulness is a strong hypothesis and defeated every candidate tried:
  `ℂ × ℂ`, `ℂ[X] × ℂ[X]`, the `d = 0` and scalar `d = 1` cases).
* RECOMMENDATION to the operator (statement change, NOT made unilaterally):
  add `[StarModule ℂ A]` to `Challenge.ov_completeness`. That one instance
  argument turns the labelled `sorry` into
  `ov_completeness_of_starModule …` verbatim. Per faithful-or-wipe the frozen
  statement was left untouched.

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

## Proven (no `sorry`, in `OV/Proofs.lean` — the 2026-07-28 proof phase)

* `psd_two`, `quad_of_le`, `herm_of_le` — a 2×2 real Loewner toolkit (PSD from
  minors via an explicit SOS identity; quadratic form and symmetry read off
  the order). No eigenvalue machinery.
* `kd₁`, `kd₂`, `kd₁_sq`, `kd₂_sq`, `kdC`, `kadison_no_inf` — the
  MACHINE-CHECKED Kadison anti-lattice instance in `M₂(ℝ)`:
  `d₁ = !![2,0;0,1]`, `d₂ = !![2,1;0,2]`, so `d₁*d₁ = !![4,0;0,1]` and
  `d₂*d₂ = !![4,2;2,5]`; both `1` and `!![31/10,0;0,0]` are positive common
  lower bounds and no greatest one exists. (A rescaling of the hand-verified
  pair in `CHALLENGE-R3.proposed.md` §3b.3, chosen so the two positive
  elements have RATIONAL square roots — the reduction consumes `star d * d`,
  so rational factors keep the whole witness in exact arithmetic.)
* `ov_dist_not_element_valued` — the tier's decisive negative, now fully
  machine-checked.
* `ov_condition_number_theorem` — both directions; `⇐` is the Eckart–Young
  rank-one `y = x - (xξ)ξ*`, with the degenerate `IsUnit y` branch handled
  honestly (it forces `ξ = 0`, hence `1 = 0` in `B`, hence `Subsingleton B`).
* `quad_id`, `isHermitian_smul_one`, `shifted_spectral`,
  `posSemidef_shift_iff`, `ov_cnt_recovers_scalar` — the scalar base case.
  **Courant–Fischer was NOT needed**: `A - t·1` is unitarily conjugate to
  `diagonal (λ - t)` via `Matrix.IsHermitian.spectral_theorem`, and
  `Matrix.posSemidef_diagonal_iff` finishes. This closes the dependency
  flagged in `Conditioning/SWEEP.md` S1 for this statement.
* `ov_lojasiewicz_order` — the symbolic FALLBACK form.
* `lift_ncMonomial`, `star_lift`, `basisFreeMonoid_eq`, `ncPoly_ne_zero`,
  `ov_completeness_of_star_scalars`, `ov_completeness_of_starModule` — the
  completeness machinery (see the gap note at the top).

## Sorry ledger (every sorry labelled)

| Statement | File | Label |
|---|---|---|
| `ov_license` (MSY iff-chain, positivity-corrected) | `Challenge.lean` | DECLARED-OPEN (frontier; true for `B = ℂ`, `Mₚ(ℂ)`). Not attempted per steering. |
| `ov_completeness` (alignment ⇒ structural cause) | `Challenge.lean`, `OV/Proofs.lean` | TARGET-still-open — ONE labelled `sorry`; missing hypothesis identified exactly (`hscal` / `[StarModule ℂ A]`), conditional forms proven |
| `ov_condition_number_theorem` | `Challenge.lean` | **PROVEN** in `OV/Proofs.lean` |
| `ov_cnt_recovers_scalar` | `Challenge.lean` | **PROVEN** in `OV/Proofs.lean` |
| `ov_dist_not_element_valued` | `Challenge.lean` | **PROVEN** in `OV/Proofs.lean` |
| `ov_lojasiewicz_order` | `Challenge.lean` | **PROVEN** in `OV/Proofs.lean` |
| `OV/CHALLENGE-R3.proposed.lean` (6 sorries) | proposal document | superseded by `Challenge.lean` + `OV/Proofs.lean`; kept as the provenance record. Deleting it would drop the tier's sorry count by 6 — operator's call. |

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
`Proofs.lean` (**the 2026-07-28 proof phase: 4 headlines proven, 1 labelled
`sorry`**), `COMPARATOR-ROWS.md` (rows for the orchestrator to apply),
`CHALLENGE-R3.proposed.{lean,md}` (provenance). `lake build OV` and
`lake build Challenge` green; `Challenge.lean` untouched by this agent.

## SIGNED OFF (historical: the review gate this tier was held at)

All six statements below were PROPOSALS under the R3 charter hard gate; the
operator SIGNED THEM OFF on 2026-07-28 and they are now live in
`Challenge.lean`. Text retained for provenance. Justification,
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
