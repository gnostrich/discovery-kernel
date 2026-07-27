# discovery-kernel

Certified detectors of exact structure in numerical data — from PSLQ to
operator-valued.

A Lean 4 / Mathlib repository certifying the soundness of rank-drop discovery
algorithms (PSLQ-class integer-relation detectors), organized as a four-tier
ladder:

* **R0 — scalar license** (Kronecker 1881): finite Hankel rank ⟺ rational
  generating function ⟺ finitely many atoms.
* **R1 — PSLQ**: exact-arithmetic core (CSV/HJLS normalization), termination
  bound, and the empirical-input theorem — a report on precision-`p` input
  with coefficient bound `M` is genuine, not a numerical artifact.
* **R2 — `DiscoveryKernel`**: the organizing typeclass (carrier, genericity
  predicate, drop observable, license theorem). R1 instantiates it.
* **R3 — operator-valued license, STATEMENTS ONLY**: MSY-shaped operator-valued
  soundness and a free-Ax–Schanuel-shaped completeness statement. These stay
  `sorry` by design; the deliverable is statements that compile.

**The claims of this repository are exactly the statements in
[`Challenge.lean`](Challenge.lean); see [`STATEMENTS.md`](STATEMENTS.md)** —
including the "What we do NOT claim" section (no R3 proofs, no floating-point
claims, no LLL-formalization novelty, no claim that R2 is a contribution).

## Layout

```
Challenge.lean    — the statement registry (all headlines `sorry`; solutions live tier-side)
STATEMENTS.md     — statements verbatim + non-claims + dated changelog
R0_Kronecker/  R1_PSLQ/  R2_Detector/  R3_OV/   — tier directories (Defs, proofs, AGENTS.md, TIER-STATUS.md)
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
