# R1 dependency verdict — Hex library

Date: 2026-07-27. Author: R1 tier agent. Status: **HEX-UNAVAILABLE** (for
this repository's pin; see rationale — availability upstream is real, the
verdict is about usability here).

## What was found (verified 2026-07-27)

The Hex library is real, public, and released:

* Aggregator: `https://github.com/leanprover/hex` — "Verified computational
  algebra in Lean 4". Announced in Leonardo de Moura's FLoC 2026 talk
  (https://leodemoura.github.io/static/floc26/): "Hex is a Lean library for
  computational algebra: LLL lattice reduction, Gram–Schmidt, matrix row
  reduction, polynomial factorization. Every algorithm is proved correct in
  Lean."
* License: **Apache-2.0** (verified from `LICENSE` in the aggregator repo) —
  MIT-compatible; licensing is NOT the blocker.
* Structure: Mathlib-free computational cores (`hex-lll`,
  `hex-gram-schmidt`, `hex-matrix`, …) plus separate `*-mathlib`
  correspondence layers (`hex-lll-mathlib`, `hex-gram-schmidt-mathlib`, …).
* Pins verified from the repos on 2026-07-27:
  - every Hex repo's `lean-toolchain` = `leanprover/lean4:v4.32.0-rc1`;
  - `hex-lll-mathlib` requires `mathlib rev = v4.32.0-rc1-patch1` and pins
    the full Hex closure by SHA (e.g. `hex-lll @
    a73f188bbd7ea48c4a1bb1e6d608b4f131026512`, `hex-gram-schmidt @
    6bae0c6ed6c19c44956dc69eb31487fc3596f01d`).

## Verdict: HEX-UNAVAILABLE (for this repo's frozen pin)

1. **Toolchain/Mathlib pin conflict (hard).** This repository pins Lean
   `v4.32.0` (release) + Mathlib `v4.32.0`. Hex pins Lean `v4.32.0-rc1` +
   Mathlib `v4.32.0-rc1-patch1`. Hex's own lakefiles state: "Lake does not
   reconcile mismatched revisions of a package required at more than one
   point in the graph." Requiring `hex-lll-mathlib` would put TWO mathlib
   revs in one build graph; the only cure is repinning the whole project's
   Mathlib to `v4.32.0-rc1-patch1`, which is a root-level decision the R1
   agent is not authorized to make (and would perturb R0/R2/R3 builds and
   the cached toolchain).
2. **Fit is partial anyway.** Hex ships LLL over ℤ and integer Gram–Schmidt.
   The R1 mission is a PSLQ-class detector in the CSV/HJLS normalization
   whose state carries *rational* Gram–Schmidt data of a projected lattice,
   with a bespoke swap strategy — not LLL. At most Hex's Gram–Schmidt would
   be reused, and the self-contained rational replacement is small.
3. **No-external-deps posture.** The project pins plain Mathlib; an external
   dependency needs strong justification. Given (1) and (2), there is none.

## Fallback (adopted)

Self-contained rational linear algebra inside `R1_PSLQ/` over `ℚ`, on plain
Mathlib v4.32.0: functions `Fin n → ℚ`, Mathlib `Matrix`/`Finset.sum`
primitives, hand-rolled Gram–Schmidt data where needed. No `Float`. No new
`require` in `lakefile.toml`.

## Addendum 2026-07-27 (steering change): certified-positivity schema verdict

Studied `/workspace/certified-positivity` (FROZEN, read-only; pins Lean
v4.28.0 vs our v4.32.0). Findings:

* `TierR.checkPDq_sound` (`lean/R_B1.lean:32`, restated in
  `Challenge.lean:235`): the schema is a **decidable Bool check over exact
  rational data** (`checkPDq M := decide (Mᵀ = M ∧ ∀ k, 0 < (leadingSubRat
  M k).det)`) plus a **soundness theorem transferring `= true` to the real
  predicate** (`IsPDq (M.map Rat.cast)`), via a `rfl`-level
  cast-commutation lemma (`leadingSubRat_cast`) and `norm_cast`.
* Rational-enclosure / margin-transfer schemas: explicit rational margin
  constants lower-bounding real quadratic forms (`true_kernel_grid_margin`,
  `gershgorin_margin`), i.e. exact-side computation + explicit ε covering
  the enclosure error.

**Verdict: ADAPT** (schema-level port; no code import). Literal import is
out (toolchain v4.28.0 vs v4.32.0; its modules import repo-local
`RequestProject.*`/`Horizon`). What R1 adapts:
1. the Bool-check + soundness shape → `R1.checkRelation xq m : Bool :=
   decide (m ≠ 0 ∧ ∑ i, (m i : ℚ) * xq i = 0)` with
   `checkRelation_sound : checkRelation xq m = true → IsIntRelation xq m`
   (executable certificate checker for the core's reports), and the
   Option-valued analogue `pslq x fuel = some m → IsIntRelation xq m`;
2. the margin-transfer shape → already embodied in our
   `pslq_empirical_sound` (exact ℚ-relation + precision `p` + coefficient
   bound `M` gives the explicit real margin `ε = n·M·p`, and separation
   transfers to an exact real relation). Cast-transfer is done in the
   `push_cast`/`norm_cast` style of `checkPDq_sound`.

## Addendum 2026-07-27 (steering change): prior-art negative on PSLQ

**RECORDED NEGATIVE (as of 2026-07-27): no formalization of PSLQ (or HJLS,
or any integer-relation-finding algorithm) in any proof assistant was
found** — not in Lean/Mathlib, Isabelle/AFP, Coq/Rocq, or HOL.

Search terms used (WebSearch, 2026-07-27):
1. "PSLQ formalization proof assistant Lean Isabelle Coq verified integer
   relation algorithm"
2. `"PSLQ" OR "HJLS" OR "integer relation" formalized "Archive of Formal
   Proofs" OR mathlib OR AFP verified`
3. `"verified PSLQ" OR "formally verified integer relation" OR "PSLQ" Coq
   Rocq formalisation`

Findings: only unverified implementations (Wolfram, Go implementation
`predrag3141/PSLQ`, mpmath etc.) and the mathematical analysis literature
(Ferguson–Bailey–Arno Math. Comp. 68 (1999); Chen–Stehlé–Villard ISSAC
2013; Chen's "PSLQ for empirical data"). Known *adjacent* art, none of it
PSLQ: LLL soundness + polynomial running time in Isabelle/HOL (Thiemann et
al., AFP, 2018–2020); LLL for Lean via Hex (assessed above, FLoC 2026);
NP-hardness reductions for lattice problems in Isabelle (arXiv:2306.08375).
Caveat recorded: absence of evidence from three web searches, not a proof
of nonexistence.

## Revisit condition

If the orchestrator ever repins the repository to Lean/Mathlib
`v4.32.0-rc1(-patch1)`, or Hex releases a tag on Mathlib `v4.32.0` final,
HEX-USABLE becomes viable with pins: `hex-lll-mathlib @
c10d6681dee9a4f963c1035bcbe34fc3eb60a769` (and its closure as listed in that
repo's `lakefile.toml`). File a note to the orchestrator; do not repin
unilaterally.
