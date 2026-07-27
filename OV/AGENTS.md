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
