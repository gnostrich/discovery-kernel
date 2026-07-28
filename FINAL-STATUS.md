# FINAL-STATUS — discovery-kernels

Date: **2026-07-28**. Toolchain: Lean 4 `v4.32.0`, Mathlib `v4.32.0` (pinned
in `lake-manifest.json`). CI: `lake build` + `comparator/comparator.py` on
every push and PR.

**Repository state: 14 of 15 registry headlines proven and audited; comparator
PASS; CI green.** The one unproven headline, `ov_license`, is DECLARED-OPEN by
design (the Mai–Speicher–Yin frontier) and is not claimed. No `Float`, no `native_decide`, no allowlist extension anywhere in
the repository. Every proven solution depends on exactly
`[propext, Classical.choice, Quot.sound]`.

## The claim

Conditioning is inverse distance to ill-posedness (Condition Number Theorem,
Demmel 1987; Bürgisser–Cucker 2013), so `dist(x, Σ)` is a **margin**: a
certified bound `dist(x, Σ) ≥ c > 0` licenses a finite-precision computation.
This repository certifies such margins at three altitudes — the scalar theory
(`Conditioning/`), one instance (`PSLQ/`), and the operator lift (`OV/`).

## Per-tier state

### Conditioning (headline) — COMPLETE, 6/6 proven

| headline | solution | state |
|---|---|---|
| `cond_check_sound` | `Cond.condCheck_sound` | proven |
| `cond_dist_to_illposed` | `Cond.condCheck_le_infDist` | proven |
| `cond_licenses_computation` | `Cond.condCheck_licenses_solve` | proven |
| `cond_eigenvalue_margin` | `Cond.condCheck_hermitian_eigenvalue_margin` | proven |
| `cond_margin_sharp` | `Cond.diag_dist_exact` | proven (sharpness witness) |
| `cond_gershgorin_wall` | `Cond.gershgorin_wall` | proven (sharpness witness) |

Six modules, zero sorries. The engine runs on the **exact rational Gram
matrix** `AᵀA`, which covers
arbitrary square matrices and **avoids Eckart–Young entirely** — deliberate,
since sweep S1 found that theorem already formalized in Lean 4 elsewhere.
The headline certifies a lower bound on Mathlib's own `Metric.infDist` in
Mathlib's own ℓ² operator norm.

### PSLQ (instance) — COMPLETE, 3/3 proven

| headline | solution | state |
|---|---|---|
| `pslq_partial_correct` | `R1.pslq_partial_correct` | proven |
| `pslq_lower_bound` | `R1.pslq_lower_bound` | proven |
| `pslq_empirical_sound` | `R1.pslq_empirical_sound` | proven |

Exact-arithmetic PSLQ-class core in the CSV/HJLS normalization
(Chen–Stehlé–Villard), because textbook PSLQ's `H` matrix is irrational even
on rational input. Partial correctness rests on the `y = x·B` unimodularity
invariant preserved by every certified elementary column operation, so it does
not depend on the pivot strategy. `DEPS.md` records all three sweep verdicts,
including the **prior-art negative**: no PSLQ/HJLS/integer-relation
formalization was found in any proof assistant.

### OV (lift) — 5 of 6 PROVEN (2026-07-28)

| headline | solution | state |
|---|---|---|
| `ov_completeness` | `R3.ov_completeness_of_starModule` | proven (hypothesis added, disclosed) |
| `ov_condition_number_theorem` | `R3.ov_condition_number_theorem` | proven (PRIMARY metric form) |
| `ov_cnt_recovers_scalar` | `R3.ov_cnt_recovers_scalar` | proven |
| `ov_dist_not_element_valued` | `R3.ov_dist_not_element_valued` | proven (the decisive negative) |
| `ov_lojasiewicz_order` | `R3.ov_lojasiewicz_order` | proven (FALLBACK symbolic form) |
| `ov_license` | — | **DECLARED-OPEN** (MSY frontier, not claimed) |

The FREEZE-0 `ov_license` draft was **replaced, not weakened** — it was proved
false as stated, and leaving a disproved statement in the registry was the
worse option. `ov_completeness` carries an added `[StarModule ℂ A]`, a
disclosed weakening: it was *proved* that the axiom is not derivable from
`[Ring] [StarRing] [Algebra ℂ]` (`R3.star_algebraMap_not_in_range`), and no
counterexample to the unhypothesised form is known. Notably
`ov_cnt_recovers_scalar` did **not** need Courant–Fischer, discharging the
sweep-S1 dependency flagged for it.

#### Founding thesis REFUTED, and that is the result

`OV/Cond.lean` is proven and sorry-free. The tier was opened on the thesis
that the operator-valued condition number is *an element of `B`*. Tested
deliberately, as instructed, and **disproved**:

* `globalInf_collapses` — the naive `dist_B` is identically **zero**, in the
  most favourable instance available (`B = ℝ × ℝ`, `E = id`, `x` invertible
  with `κ = 2`).
* `bvaluedDistance_not_scalar` — the repaired object does **not** collapse to
  `λ_min` or a norm: `(1,2)` and `(2,1)` share every scalar invariant but have
  distinct `B`-valued distances.
* `isMargin_diagonal_iff`, `bvaluedDistance_fails_of_no_infimum` — element-
  valued `dist_B` holds **iff** `B₊` is an inf-semilattice, which by Kadison's
  anti-lattice theorem fails over **every factor**. `dist_B` is a certificate
  *set*, not an element.

Honest residue: a dichotomy. Abelian `B` gives a fibrewise **componentwise
condition number** — occupied literature (sweep S2), no novelty. Noncommutative
`B` is not element-valued at all; the certificate-set formulation plus the
anti-lattice obstruction is what no literature was found to have.

#### Symbolic fallback (STEERING 02a) — collapse test SURVIVED

`OV/Symbolic.lean` is proven and sorry-free. It carries no metric: `Σ` is a
**discriminant** (the fibre at `t = 0` is non-invertible, taken
coefficientwise so nothing commutative is assumed), perturbation is
**deformation** in a polynomial family over `B[t]`, and distance is **order of
vanishing** — `ovVanishingOrder`, the trailing degree of the direction datum,
an integer recorded **per direction and never aggregated**.

The collapse test for this form is whether the exponent tuple is constant
across directions. Sweep S3 (`OV/SWEEP.md`) showed that test is *identical* to
the occupancy test, since a constant tuple degenerates to the single published
Łojasiewicz exponent. **The tuple is non-constant, proved twice:**

* `exponentTuple_not_constant` — over `B = ℝ × ℝ`, the family `t ↦ (t, t²)`
  has order `1` in direction `(1,0)` and order `2` in direction `(0,1)`, and
  genuinely deforms through the discriminant (`symWitness_degenerate`).
* `exponentTuple_not_constant_noncomm` — over `B = M₂(ℝ)`, the family
  `t ↦ e₁t + e₂t²` has orders `1` and `2` in directions `e₁`, `e₂`.

Note the contrast with the metric form: there the surviving content was
confined to noncommutative `B` while the abelian case fell into published
componentwise conditioning. Here the survival witness exists **in** the
noncommutative setting — exactly the gap S3 identified. On that one axis the
fallback is better positioned than the primary form.

**Boundary held**: no family was invented. A single `x ∈ Mₙ(B)` has no family,
no discriminant and no order of vanishing, so the symbolic form simply does not
apply to it — which is why both forms are stated side by side rather than one
derived from the other. Symbolic proof search over a proof library is closed
and recorded as such.

## Axiom report

Every one of the 9 proven headline solutions, and every supporting lemma
checked (20+ in Conditioning, 11 in PSLQ, 6 in OV):

```
depends on axioms: [propext, Classical.choice, Quot.sound]
```

`comparator/allowlist.toml` remains at its default; **no extension was ever
requested**. `sorryAx` is fatal for solutions and appears in none.

## Open sorries

* **Registry sorries** — all 15 headlines in `Challenge.lean` are `:= sorry`
  by construction. `Challenge.lean` is a statement registry, never a proof
  site; solutions live tier-side and are matched by definitional equality.
  These are not open problems.
* **`ov_license`** is the single headline without a solution: **DECLARED-OPEN**
  (the Mai–Speicher–Yin frontier); we do not claim it.
* **No other sorries exist in the repository.** The proved OV supporting
  layers (`OV/Cond.lean`, `OV/Symbolic.lean`), which carry both collapse-test
  verdicts, are entirely sorry-free.

## Statements changed after FREEZE-0 (all dated in STATEMENTS.md)

1. **DESCOPE (STEERING 01)** — R0 and R2 removed. The completed R2 artifact
   (frozen signature, lemma library, zero-sorry toy instance) is preserved in
   git history at the pre-descope commit rather than deleted.
2. **`pslq_partial_correct` refined** from a `True` placeholder to the real
   statement, once the core existed. Justification: the core proved strictly
   more than the registry stated, and an unstated proof is not yet a claim.
3. **`pslq_lower_bound` refined** from a `True` placeholder to the
   Borwein–Lisoněk form. Stated with an explicit index `k` rather than a `min`
   over all `j`, because the `min` form is provably the trivial bound `0` —
   packaging it that way would have been a fake theorem.
4. **Novelty claim narrowed** after sweep S1 found Eckart–Young–Mirsky, Weyl,
   Courant–Fischer and Davis–Kahan already formalized in Lean 4 outside
   Mathlib. Recorded before any Conditioning Lean was written.
5. **Conditioning section placed first** in `Challenge.lean` — which claim
   leads is itself a claim.
6. **OV element-valued thesis recorded as refuted**, with the proof.
7. **CORRECTION 2026-07-28 (STATEMENT-DEFECT).** The claim "Mathlib has no
   Gershgorin" was FALSE — `Mathlib/LinearAlgebra/Matrix/Gershgorin.lean`
   exists (`Matrix.eigenvalue_mem_ball`, `det_ne_zero_of_sum_row_lt_diag`).
   All surfaces corrected; no novelty is claimed for eigenvalue localisation
   or diagonal-dominance nonsingularity. The Rayleigh quadratic-form floor
   survives, verified. Root cause: a sweep verdict is asserted, not
   kernel-checked; absence claims are now CI-guarded by
   `comparator/sweep_check.py`. See `Conditioning/SWEEP.md`.
8. **R3/OV statements signed off and landed** (2026-07-28): the disproved
   `ov_license` replaced by the refined chain, the `True` placeholder
   `ov_completeness` replaced by a real statement, and four statements added
   (PRIMARY metric CNT in `B`-valued form, its scalar sanity condition, the
   element-valued negative, the FALLBACK symbolic Łojasiewicz form). Registry
   grew from 11 to 15 headlines; the 9 proven solutions are unaffected.

## What we do not claim

See `STATEMENTS.md`. In brief: no priority on Eckart–Young–Mirsky, Weyl,
Courant–Fischer or Davis–Kahan; no floating-point or rounding-error novelty;
no LLL novelty; no control-theory claim; **soundness only, never
completeness**, for every checker in the repository; and no claim that the
operator-valued condition number is an element of `B` — we claim and prove the
opposite.
