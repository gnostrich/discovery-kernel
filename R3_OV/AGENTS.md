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
   `R3_OV/VOCAB.md`: what exists vs. what must be defined. Be honest about
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
