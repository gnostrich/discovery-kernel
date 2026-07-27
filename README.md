# discovery-kernel

Certified detectors of exact structure in numerical data — from PSLQ to
operator-valued.

A Lean 4 / Mathlib repository certifying the soundness of rank-drop discovery
algorithms (PSLQ-class integer-relation detectors), organized as two tiers:

* **R1 — PSLQ**: exact-arithmetic core (CSV/HJLS normalization), termination
  bound, and the empirical-input theorem — a report on precision-`p` input
  with coefficient bound `M` is genuine, not a numerical artifact. This is
  the point of the tier.
* **R3 — operator-valued license, STATEMENTS ONLY**: MSY-shaped operator-valued
  soundness and a free-Ax–Schanuel-shaped completeness statement. These stay
  `sorry` by design; the deliverable is statements that compile. Human review
  gates every R3 statement.

The scalar license (Kronecker's theorem and the realization-theory spine)
lives in the sibling repository
[`gnostrich/realization-lean`](https://github.com/gnostrich/realization-lean).
The decidable-check-soundness and certificate schemas this repo's empirical
theorem is shaped after live in the frozen prior-art repository
[`gnostrich/certified-positivity`](https://github.com/gnostrich/certified-positivity).

**The claims of this repository are exactly the statements in
[`Challenge.lean`](Challenge.lean); see [`STATEMENTS.md`](STATEMENTS.md)** —
including the "What we do NOT claim" section.

## Layout

```
Challenge.lean    — the statement registry (all headlines `sorry`; solutions live tier-side)
STATEMENTS.md     — statements verbatim + non-claims + dated changelog
PSLQ/  OV/  — tier directories (Defs, proofs, AGENTS.md, TIER-STATUS.md)
comparator/       — statement-fidelity (definitional-equality) + axiom-allowlist audit, run in CI
scripts/          — Aristotle prover helper (API key from env, never committed)
```

## Build

```
lake exe cache get
lake build
python3 comparator/comparator.py
```

Toolchain: Lean 4 `v4.32.0`, Mathlib `v4.32.0` (pinned in `lake-manifest.json`).

License: MIT.
