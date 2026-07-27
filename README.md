# discovery-kernel

Certified distance to ill-posedness, in Lean 4 / Mathlib.

A problem maps input data to an answer. Some inputs are **ill-posed**: an
arbitrarily small perturbation changes the answer discontinuously. Write `Σ`
for the set of ill-posed inputs — singular matrices for matrix inversion,
polynomials with a repeated root for root-finding, vectors admitting a shorter
relation for integer-relation detection. The condition number `κ(x)` measures
error amplification and is infinite exactly on `Σ`, and by the **Condition
Number Theorem** (Demmel 1987, Numer. Math. 51, 251–289; Bürgisser–Cucker,
*Condition: The Geometry of Numerical Algorithms*, Springer 2013),

```
κ(x) = ‖x‖ / dist(x, Σ)
```

Conditioning is inverse distance to ill-posedness. So `dist(x, Σ)` is a
**margin**: a certified bound `dist(x, Σ) ≥ c > 0` licenses a finite-precision
computation, because data accurate to better than `c` yields a provably
correct answer. That is the theorem every numerical claim implicitly leans on.

This repository certifies such margins at three altitudes — one theory, not
three projects.

* **`Conditioning/` — the scalar theory (headline).** Certified lower bounds on
  `dist(x, Σ)` for `Σ` = singular matrices, each paired with an **executable
  checker proven sound** over exact rational arithmetic, plus **sharpness
  witnesses**: certified inputs where the bound is exactly zero, so the
  library certifies both the floor and where the floor degenerates.
* **`PSLQ/` — one instance.** Integer-relation detection, `Σ` = vectors
  admitting a shorter relation. Exact-arithmetic PSLQ-class core, a
  Borwein–Lisoněk termination bound, and the empirical-input theorem: input
  known to precision `p` with coefficient bound `M` ⟹ the reported relation is
  genuine, not a rounding artifact.
* **`OV/` — the operator lift.** Statements only, under a human-review gate.
  Both collapse tests were run and reported: the *element-valued* condition
  number is **refuted** (proved — `dist_B` is a certificate set, not an element
  of `B`), while the symbolic Łojasiewicz order-of-vanishing form **survives**.

**Status: 9 of 9 required headlines proven; comparator PASS; CI green.** Every
proven solution depends on exactly `[propext, Classical.choice, Quot.sound]`.
No `Float`, no `native_decide`, no allowlist extension anywhere.

## The claims are the statements

[`Challenge.lean`](Challenge.lean) is a **statement registry**: every headline
is `:= sorry` permanently, solutions live tier-side, and
[`comparator/`](comparator/) checks that each solution's type is
*definitionally equal* to the registry statement and audits `#print axioms`
against a per-theorem allowlist (`sorryAx` fatal for solutions). CI runs it on
every push and PR.

Prose in this repository never claims anything `Challenge.lean` does not
state. [`STATEMENTS.md`](STATEMENTS.md) carries the statements verbatim, a
dated changelog, and an explicit **"What we do NOT claim"** section — including
no priority on Eckart–Young–Mirsky, Weyl, Courant–Fischer or Davis–Kahan
(already formalized in Lean 4 elsewhere), no Łojasiewicz-on-`σ_min` novelty
(published for polynomial matrices), no floating-point or LLL novelty, and
**soundness only, never completeness**: every checker theorem says "says yes ⟹
true", never the converse.

Three blocking prior-art sweeps ran *before* the corresponding Lean was
written ([`Conditioning/SWEEP.md`](Conditioning/SWEEP.md),
[`OV/SWEEP.md`](OV/SWEEP.md)); two of them narrowed what this repository is
allowed to claim. [`FINAL-STATUS.md`](FINAL-STATUS.md) records the per-tier
state, the axiom report, the open sorries, and every statement that changed
after FREEZE-0 with its justification.

## Layout

```
Challenge.lean    — the statement registry (all headlines `sorry`; solutions live tier-side)
STATEMENTS.md     — statements verbatim + non-claims + dated changelog
FINAL-STATUS.md   — per-tier state, axiom report, open sorries, statement changes
Conditioning/     — headline tier: certified margins, sound checkers, sharpness witnesses
PSLQ/             — the instance: exact core, termination bound, empirical-input theorem
OV/               — the operator lift: statements only, human-review gated
comparator/       — definitional-equality statement check + axiom-allowlist audit, run in CI
scripts/          — Aristotle prover helper (API key from env, never committed)
```

Prior art adapted at schema level (never imported — its Lean pin differs):
[`gnostrich/certified-positivity`](https://github.com/gnostrich/certified-positivity),
frozen, for the `checkPDq_sound` checker-soundness shape, `gershgorin_margin`,
and the `three_grid_last_row_gershgorin_zero` sharpness-witness pattern.

## Build

```
lake exe cache get
lake build
python3 comparator/comparator.py
```

Toolchain: Lean 4 `v4.32.0`, Mathlib `v4.32.0` (pinned in `lake-manifest.json`).

License: MIT.
