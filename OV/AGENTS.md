# R3 agent — operator-valued license (STATEMENTS ONLY)

Persistent charter + memory for the R3 tier agent. Read this fully at session
start; append to MEMORY after every significant step. Obey the root
`AGENTS.md` policies.

## Mission

Statements only; proofs are OUT OF SCOPE by design and `sorry` is the correct
final state for this tier's headlines.

1. **VOCAB.md (hour-one-class blocker for this tier):** survey what Mathlib
   has toward von Neumann algebras / C*-algebras, conditional expectation,
   operator-valued measures, free probability (expect: little). Write
   `OV/VOCAB.md`: what exists vs. what must be defined. Be honest about
   gaps.
2. Build the MINIMAL definitional layer to state (not prove): `B`-valued
   Hankel-type rank; rationality of a `B`-valued resolvent; atomic support of
   an `E_B`-conditioned measure. Prefer stating over abstract structures with
   hypotheses to building deep theory. FREEZE-0 seeded `Defs.lean` with
   candidates (left-module Hankel rank, finite linear realization,
   finitely-atomic moment form) — refine or replace, with docstrings naming
   the informal object and citation (Mai–Speicher–Yin; Schützenberger for
   realizations).
3. Refine the Challenge.lean R3 headlines (`ov_license` MSY-shaped iff chain;
   `ov_completeness` free-Ax–Schanuel-shaped: every genuine OV alignment has
   a structural cause), keeping them `sorry`.

## HUMAN-REVIEW GATE (hard rule)

R3's Challenge.lean entries require human review before merge to main. Post
proposed statements in `TIER-STATUS.md` under "PENDING HUMAN REVIEW" and hold
the merge until the operator approves. This is the one tier where a
plausible-but-wrong statement corrupts the thesis silently instead of
failing CI.

## MEMORY (append-only, dated)

* 2026-07-27 — Tier initialized at FREEZE-0 with draft `Defs.lean`
  (simplification flags in docstrings) and a draft `ov_license` shape in
  Challenge.lean; both count as PENDING HUMAN REVIEW.
* 2026-07-27 — Mathlib v4.32 survey delivered (`VOCAB.md`): C*-positivity
  language, `FreeAlgebra`/`FreeMonoid`+word basis, f.g.-module framework
  EXIST; vN algebras are a bare skeleton; operator-algebraic `E_B`, OV
  measures/atoms, recognizable series/Hankel MUST-DEFINE; free probability
  absent (OUT-OF-SCOPE, abstracted into hypotheses).
* 2026-07-27 — DECISION: FREEZE-0 `ov_license` judged unkeepable as stated:
  (a) span-of-shifts f.g. rank def has a Noetherian gap vs realizations —
  replaced by Fliess stable-submodule form (`HasFiniteOVHankelRankStable`);
  (b) unconditional realization ⟺ atomic is FALSE (cos nθ over ℝ; Jordan
  block n·λⁿ over ℂ) — positivity hypotheses added (`IsOVMomentSequence`,
  `StarOrderedRing`), atomicity star-corrected (`IsFinitelyAtomicOVStar`,
  atoms-in-B kept deliberately — L∞[0,1] rank-1 diffuse-scalarization
  witness). Details in `CHALLENGE-R3.proposed.md`.
* 2026-07-27 — New defs in `Vocab.lean` (extends `Defs.lean` untouched, so
  live Challenge.lean semantics unchanged); refined `ov_license` +
  first real `ov_completeness` (alignment ⇒ structural cause; genericity =
  faithfulness of `E` + self-adjoint tuple; degree-local cause) stated in
  `CHALLENGE-R3.proposed.lean` — compiles with exactly 2 sorry warnings;
  `lake build OV` and `lake build Challenge` green (proposal builds as
  module `OV.«CHALLENGE-R3.proposed»` under the glob). Proposals posted
  under PENDING HUMAN REVIEW in `TIER-STATUS.md`; merge held for operator.
  Aristotle not used (statements-only tier; nothing to prove).
* 2026-07-27 — STEERING-02 received: tier REFRAMED as the operator lift of
  the new `Conditioning/` tier (B-valued Condition Number Theorem). Sorries
  are now TARGET vs DECLARED-OPEN, labelled in TIER-STATUS.md. Read
  `Conditioning/SWEEP.md` S2 (not redone).
* 2026-07-27 — `OV/Cond.lean` written and FULLY PROVED (no sorry):
  `ovInner`/`ovRayleigh`/`IsMargin`/`distB`/`IsBValuedDistance`/
  `IsDistanceCertificate`/`IsGlobalInfMargin`; `isMargin_diagonal_iff`;
  `infima_of_bvaluedDistance_diagonal`; `bvaluedDistance_fails_of_no_infimum`;
  `margin_imp_distanceCertificate`; `margin_imp_inverse_bound`.
* 2026-07-27 — COLLAPSE TESTS RUN. (a) Naive `dist_B` = global inf over Σ of
  `E(δ*δ)` PROVED ≡ 0 (`globalInf_collapses`), even with E = id, commutative
  B, well-conditioned x ⇒ definition D1 DEAD; the bound must be compressed to
  ker y. (b) Surviving object PROVED not λ_min / not a norm / not any scalar
  invariant (`bvaluedDistance_not_scalar`: (1,2) vs (2,1) over ℝ×ℝ share all
  scalar condition data, differ in dist_B). (c) NEW DECISIVE NEGATIVE: dist_B
  is NOT an element of B — diagonal reduction + Kadison anti-lattice (1951)
  ⇒ over a factor no greatest margin exists; dist_B is a CERTIFICATE SET.
  Hand-verified M₂(ℝ) witness (a₁ = diag(2,1), a₂ = [[3/2,1/2],[1/2,3/2]],
  incomparable lower bounds 1 and diag(21/20,9/10)) recorded in the .md,
  stated as TARGET `ov_dist_not_element_valued`. (d) SWEEP-S2 abelian
  collapse FIRES: for abelian B, dist_B = componentwise condition number
  (Skeel/Rohn/Higham) — no novelty in that case. Net verdict: tier survives
  narrowly with a sharper, certificate-shaped claim; element-valued framing
  refuted.
* 2026-07-27 — Three conditioning headlines added to
  `CHALLENGE-R3.proposed.lean` (`ov_condition_number_theorem`,
  `ov_cnt_recovers_scalar`, `ov_dist_not_element_valued`), all TARGET
  sorries; file compiles with exactly 5 sorry warnings; `lake build OV`
  green. Challenge.lean still untouched; merge still held for the operator.
* 2026-07-27 — STEERING-02a: directory renamed `R3_OV/` → `OV/` (imports now
  `OV.*`). Read `OV/SWEEP.md` S3 (not redone): Łojasiewicz with explicit
  exponents for σ_min of real polynomial matrices is PUBLISHED
  (arXiv 1604.02805) — no novelty claimed there; unoccupied = noncommutative
  setting + per-direction exponent tuple.
* 2026-07-27 — `OV/Symbolic.lean` written and FULLY PROVED (no sorry):
  `ovFamilyImage`, `ovVanishingOrder` (trailing degree of the direction
  datum, ℕ∞-valued, per direction), `familyFibreZero`, `IsDegenerateAtZero`
  (Σ as discriminant), `ovDatumCoeff`, `ovLeadingCertificate`,
  `ExponentTupleConstant`. Small refactor of `Cond.lean`: `ovInner`/
  `ovRayleigh`/`IsIllPosed` no longer require `[PartialOrder B]` (needed for
  polynomial coefficients); order-dependent defs moved into an inner
  `Ordered` section. Cond.lean still green, zero sorries.
* 2026-07-27 — SYMBOLIC COLLAPSE TEST RUN: **NO COLLAPSE**, proved twice.
  `exponentTuple_not_constant` (B = ℝ×ℝ, family t ↦ (t,t²): orders 1 and 2)
  and `exponentTuple_not_constant_noncomm` (B = M₂(ℝ), t ↦ e₁t + e₂t²:
  orders 1 and 2). The tuple is non-constant, so the form does not degenerate
  to the published single Łojasiewicz exponent — and unlike the metric form
  (whose abelian case fell into published componentwise conditioning) the
  survival witness exists in the noncommutative case. Boundary held: no
  family invented; symbolic proof search over a proof library stays CLOSED.
* 2026-07-27 — `ov_lojasiewicz_order` added to `CHALLENGE-R3.proposed.lean`
  as the FALLBACK headline, with explicit PRIMARY (metric) / FALLBACK
  (symbolic) marking in the section headers; 6 statements, 6 sorry warnings,
  no errors; `lake build OV` green. Sorry ledger in TIER-STATUS.md updated
  (all labelled TARGET / DECLARED-OPEN).
* 2026-07-28 — STATEMENTS SIGNED OFF by the operator; tier switched from
  statements-only to PROOF PHASE. `OV/Proofs.lean` written. **4 of the 5
  TARGETs PROVEN**, all with types `isDefEq` to the frozen `Challenge.lean`
  entries and axioms exactly `[propext, Classical.choice, Quot.sound]`:
  `ov_dist_not_element_valued`, `ov_condition_number_theorem`,
  `ov_cnt_recovers_scalar`, `ov_lojasiewicz_order`. `lake build OV` green.
  Comparator rows written to `OV/COMPARATOR-ROWS.md` (agent does not edit
  `comparator/*`). No allowlist extension needed.
* 2026-07-28 — API notes for successors. (a) The Loewner order lives in
  `Mathlib/Analysis/Matrix/Order.lean`, scoped `MatrixOrder`:
  `Matrix.le_iff : A ≤ B ↔ (B - A).PosSemidef`,
  `Matrix.nonneg_iff_posSemidef`, and the `StarOrderedRing` instance needs
  `RCLike 𝕜` + `Fintype n`. (b) `Matrix.PosSemidef` is stated with `Finsupp`
  sums; use `PosSemidef.of_dotProduct_mulVec_nonneg` /
  `PosSemidef.dotProduct_mulVec_nonneg` for the `Fintype` quadratic form.
  (c) `Basis` now lives in namespace `Module` —
  `Module.Basis.repr_symm_apply`, not `Basis.repr_symm_apply`.
  (d) There is NO `star_list_prod`; do `star` of a word by
  `induction w using FreeMonoid.recOn`.
* 2026-07-28 — **Courant–Fischer was NOT needed** for
  `ov_cnt_recovers_scalar` (contra the dependency flagged in
  `Conditioning/SWEEP.md` S1). The min-characterisation is obtained directly:
  `shifted_spectral` shows `A - t·1 = U · diagonal (λ - t) · U*` from
  `Matrix.IsHermitian.spectral_theorem`, then
  `IsUnit.posSemidef_star_right_conjugate_iff` + `posSemidef_diagonal_iff`
  give `(A - t·1).PosSemidef ↔ ∀ i, t ≤ λ i`. Cheap and exact.
* 2026-07-28 — The `M₂(ℝ)` Kadison witness was RESCALED for the machine proof:
  `d₁ = !![2,0;0,1]`, `d₂ = !![2,1;0,2]` giving `a₁ = !![4,0;0,1]`,
  `a₂ = !![4,2;2,5]`, common lower bounds `1` and `!![31/10,0;0,0]`. Reason:
  `bvaluedDistance_fails_of_no_infimum` consumes `star d * d`, not `a`, and
  the §3b.3 pair `diag(2,1)` / `[[3/2,1/2],[1/2,3/2]]` has IRRATIONAL square
  roots. Same anti-lattice argument, all-rational data.
* 2026-07-28 — **`ov_completeness` NOT PROVED — one honest labelled `sorry`,
  reported.** The full argument is machine-checked as
  `ov_completeness_of_star_scalars` (extra hypothesis
  `hscal : ∀ z, ∃ z', star (algebraMap ℂ A z) = algebraMap ℂ A z'`) and as
  `ov_completeness_of_starModule` (`[StarModule ℂ A]`), both `sorry`-free.
  The frozen statement assumes only `[Ring A] [StarRing A] [Algebra ℂ A]`,
  which does not imply `hscal` — and that is now PROVED, not asserted:
  `star_algebraMap_not_in_range` (sorry-free) builds `TwistCC = ℂ × ℂ` with
  `algebraMap z = (z,z)`, `star (s,t) = (s, conj t)` — a lawful instance pair
  with `star (algebraMap I) = (I,-I)` outside the range. Consequence: the ℂ-span
  of the words is not `star`-stable, so `star a ∉ W` and `hfaith` cannot be
  applied to it. NO counterexample to the headline itself was found
  (`ℂ×ℂ`, `ℂ[X]×ℂ[X]`, `d = 0`, scalar `d = 1` all fail to break it —
  faithfulness is strong). Statement NOT adjusted (faithful-or-wipe);
  recommended operator fix is adding `[StarModule ℂ A]`.
* 2026-07-28 — Aristotle jobs (helper confirmed FIXED; both submitted early,
  local work kept in flight, never idled on):
  `be6001be-e0d9-4334-96e5-a61eea049814` (standalone `ov_cnt_recovers_scalar`)
  — **verdict: SUPERSEDED**, proved locally first, still RUNNING at session
  end, nothing fetched, nothing trusted, no output used.
  `80d5865b-4baa-4b78-b759-591f11ae84b6` (standalone `ov_completeness`, plus a
  follow-up `ask` carrying the `hscal` analysis) — **verdict: NO RESULT**,
  still RUNNING at session end, nothing fetched, nothing trusted. Successor:
  poll these two before re-submitting; if `80d5865b…` returns a proof of
  `ov_completeness` WITHOUT adding hypotheses, treat it as untrusted, re-verify
  locally, and re-examine the `hscal` analysis above — it would mean the
  analysis missed a route.
