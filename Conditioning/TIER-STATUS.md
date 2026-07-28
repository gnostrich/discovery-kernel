# TIER-STATUS — CONDITIONING — certified distance to ill-posedness

Updated 2026-07-27 (first session; engine + checkers + bridge + witnesses all
landed).

## Proven (sorry-free, axioms exactly `[propext, Classical.choice, Quot.sound]`)

### Engine — `Conditioning/Gershgorin.lean` (Mathlib HAS Gershgorin; see SWEEP.md correction 2026-07-28)

* `gershgorin_rayleigh_floor` — diagonal dominance with margin `μ` gives
  `μ‖x‖² ≤ xᵀMx` for real symmetric `M`. No sign assumption on `μ`. Proved
  from scratch (schema adapted from the frozen `certified-positivity`
  `R5.gershgorin_margin`; no code imported, pins differ).
* `gershgorin_disc` — Gershgorin's **circle theorem** for real eigenvalues of
  an arbitrary square real matrix. Proved by the maximal-coordinate argument.

### Spine — `Conditioning/Defs.lean`, `Conditioning/Margin.lean`

* `quadForm_gram` — `vᵀ(AᵀA)v = ‖Av‖²`. The transport that turns a
  symmetric-only Rayleigh engine into a `σ_min` engine for **arbitrary** square
  matrices.
* `sigmaMinGE_of_gram_floor`, `det_ne_zero_of_sigmaMinGE`,
  `not_mem_sigmaSing_of_sigmaMinGE`.
* `abs_eigenvalue_ge_of_sigmaMinGE` — `σ_min(A) ≥ c ⟹ c ≤ |λ|` for every real
  eigenvalue.
* `distGE_of_sigmaMinGE` — **the distance theorem**: `σ_min(A) ≥ c` implies no
  perturbation of spectral norm `< c` makes `A` singular. This is the lower
  bound half of the Condition Number Theorem, proved in four lines; it does not
  use and does not assume Eckart–Young.
* `not_distGE_of_singular_perturbation` — the contrapositive tool that makes
  sharpness witnesses possible without Eckart–Young.
* `distGE_zero_vacuous` — **honesty lemma**: `DistGE A 0` holds for every
  matrix, so a zero certificate says nothing.
* `specNormLe_inv_of_sigmaMinGE` — `‖A⁻¹‖ ≤ 1/c`, hence `κ₂(A) ≤ ‖A‖/c`.
* `solve_error_bound` — certified forward error for `A x = b`.

### Executable checkers — `Conditioning/Checker.lean`

* `condCheck` (exact `ℚ`, `decide`-based, **no `Float`, no `native_decide`**)
  with `condCheck_sound`, `condCheck_distGE`, `condCheck_abs_eigenvalue`,
  `condCheck_det_ne_zero`, `condCheck_inv_bound`, `condCheck_licenses_solve`.
* `discCheck` with `discCheck_abs_eigenvalue`; and
  `det_ne_zero_of_strict_diag_dominance` (Levy–Desplanques).
* Cast infrastructure: `toReal_gramQ`, `gershRadius_toReal`, `transpose_gramQ`,
  `gershRadiusQ_eq`.

### Faithfulness bridge — `Conditioning/Bridge.lean`

* `norm_euc_sq` — `sqNorm` is Mathlib's `EuclideanSpace` norm, squared.
* `specNormLe_of_l2_opNorm_le`, `sigmaMinGE_iff_norm` — the elementary
  formulations are the textbook ones, not weakenings.
* `le_infDist_sigmaSing_of_distGE` and `condCheck_le_infDist` — the executable
  check certifies a lower bound on Mathlib's genuine
  `Metric.infDist (·) (SigmaSing n)` in Mathlib's **ℓ² operator norm**.
* `isEigenvalue_eigenvalues`, `condCheck_hermitian_eigenvalue_margin` — wired
  to Mathlib's own `Matrix.IsHermitian.eigenvalues`.

### Sharpness witnesses — `Conditioning/Sharpness.lean`

* `diag_dist_exact` — **the certified floor is exactly the distance** on
  `!![3,0;0,5]`: the engine's output is exactly `3`, and `dist = 3` on the
  nose (upper bound by explicit certified perturbation, not Eckart–Young).
* `gershgorin_wall` — **the engine's wall**: on `!![1,1;0,1]` the Gram matrix's
  first-row diagonal-dominance margin is **exactly zero** (an equality between
  exact rationals), so `condCheck` certifies only `c = 0` — which is vacuous —
  and yet `dist ≥ 1/2` is certified by a stronger route.
* `singular_dist_zero` — the contrasting case: on `!![1,1;1,1]` the truth is
  `dist = 0` and no positive certificate can exist.

## Sorry

* **Nothing in `Conditioning/*.lean` is `sorry`** except
  `CHALLENGE-COND.proposed.lean`, whose six statements are `:= sorry` **by
  design** (it is a proposal for the statement registry; that file states, it
  never proves).

## Honest caveats (stated, not hidden)

* **Soundness only, never completeness.** Both checkers. A `false` answer means
  "this engine cannot certify it", never "the bound is false".
* **A zero certificate is vacuous**, and this is proved
  (`distGE_zero_vacuous`), not merely asserted. `gershgorin_wall` is the
  certified instance where the engine produces exactly that.
* **`discCheck` is deliberately not wired to `DistGE`.** Eigenvalue margin is
  not distance-to-singularity for non-normal matrices, and a real matrix may
  have no real eigenvalues. Doing so would be a fake theorem.
* **Only the RHS is perturbed** in `solve_error_bound`. The full
  perturbed-`A` forward-error bound needs a vector-norm triangle inequality and
  was not attempted. The *invertibility* half of it is proved.
* **No novelty claimed for Eckart–Young–Mirsky / Weyl / Courant–Fischer /
  Davis–Kahan** (SWEEP.md S1: already in Lean 4 in
  `YuanheZ/lean-stat-learning-theory`). None of them is used; only the easy
  lower-bound direction is needed and it is proved from scratch here.
* **The ℓ² operator-norm scope is a real footgun.** It is opened in exactly two
  places (`Bridge.lean`, and one `section` in the proposed Challenge block) and
  nowhere else in the tier.
* **`gershgorin_rayleigh_floor` with `μ ≤ 0`** is true and vacuous; said so in
  its docstring.

## Build state

* Every module elaborates with `lake env lean Conditioning/<Mod>.lean`, exit 0,
  no errors. `Margin`, `Sharpness`, `Bridge` emit only style lints.
* `CHALLENGE-COND.proposed.lean` elaborates with exactly its six by-design
  `sorry` warnings.
* Comparator `isDefEq` hand-run: all six challenge/solution pairs match.
* `#print axioms`: the default triple on all six solutions and on 20 supporting
  lemmas. No allowlist extension requested.

## Blocked

* **`lakefile.toml` has no `Conditioning` library** — orchestrator action
  required; exact TOML and the glob caveat are in
  `Conditioning/COMPARATOR-ROWS.md`. This is the only blocker, and it does not
  block verification (see above).

## Deliverables for the orchestrator

* `Conditioning/CHALLENGE-COND.proposed.lean` — the six headline statements,
  compiling, `:= sorry`, to be placed **first** in `Challenge.lean`.
* `Conditioning/CHALLENGE-COND.proposed.md` — justification per headline, the
  vacuity register, and a proposed dated `STATEMENTS.md` changelog paragraph.
* `Conditioning/COMPARATOR-ROWS.md` — six `headlines.toml` rows, the
  `AxiomCheck.lean` additions, the required `lakefile.toml` entry, and the
  local verification table.
