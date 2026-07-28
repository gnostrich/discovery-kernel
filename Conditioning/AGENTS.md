# CONDITIONING agent — certified distance to ill-posedness

Persistent charter + memory for the Conditioning tier agent. **Read this fully
at session start**; append to MEMORY after every significant step. Obey the
root `AGENTS.md` policies. This tier is the repository's **headline claim**.

## The mathematics (self-contained; do not re-derive)

A problem maps input data to an answer. Some inputs are **ill-posed**: an
arbitrarily small perturbation changes the answer discontinuously. `Σ` denotes
the set of ill-posed inputs — for matrix inversion, the singular matrices; for
root-finding, polynomials with a repeated root; for positive-definiteness,
symmetric matrices with a zero eigenvalue; for PSLQ, vectors admitting a
shorter relation. The condition number `κ(x)` measures error amplification and
is infinite exactly on `Σ`. The **Condition Number Theorem** (Demmel, *On
condition numbers and the distance to the nearest ill-posed problem*, Numer.
Math. 51 (1987) 251–289; canonical text Bürgisser–Cucker, *Condition: The
Geometry of Numerical Algorithms*, Springer 2013) says

    κ(x) = ‖x‖ / dist(x, Σ)

— conditioning is inverse distance to ill-posedness. **Why it matters:**
`dist(x, Σ)` is a *margin*; a certified bound `dist(x, Σ) ≥ c > 0` licenses a
finite-precision computation, because data accurate to better than `c` yields a
provably correct answer.

## Mission (strict order)

1. **Read `Conditioning/SWEEP.md` first, every session.** The blocking S1/S2
   prior-art sweeps are DONE by the orchestrator and are **binding on what may
   be claimed**. Do not redo them. S1's verdict: Eckart–Young–Mirsky, Weyl,
   Courant–Fischer, Davis–Kahan **are** formalized in Lean 4 in the third-party
   `YuanheZ/lean-stat-learning-theory` (sorry-free, ICML 2026), though not in
   Mathlib and not framed as conditioning. **Claim no novelty for those.** Do
   not import that library (pin unverified). If a proof needs Eckart–Young,
   prove the specific instance — but note that the tier as built needs only the
   *easy* lower-bound direction, which is four lines.
2. **Certified lower bounds on `dist(x, Σ)`.** Start with `Σ` = symmetric
   matrices with a zero eigenvalue (`dist = λ_min`), extend to the general
   singular-matrix case. **DONE** — and the general case turned out to be
   *easier*, via the Gram transport, so the tier covers arbitrary square
   matrices.
3. **Executable checkers proven sound**: `Bool`-returning, exact `ℚ`, with
   `checker x = true → dist(x, Σ) ≥ c`. Soundness only is correct and expected;
   say so in docstrings. **DONE** (`condCheck`, `discCheck`).
4. **Sharpness witnesses** — certified concrete inputs where the bound is
   exactly zero, or exactly attained. This is the part that is more than a
   formalization. **DONE** (three witnesses).
5. **Next frontiers** (see "Open work" below): a second `Σ` (polynomials with a
   repeated root), the perturbed-`A` forward-error bound, an `n`-dimensional
   diagonal sharpness family, and a non-Gershgorin engine (Cholesky/Sylvester
   over `ℚ`) that would climb the wall witness 2 certifies.

## Hard constraints (non-negotiable)

* **Exact arithmetic (`ℚ`/`ℤ`) or interval-certified only. NO `Float`
  anywhere**, in any statement or definition.
* **`native_decide` is BANNED** unless justified in `comparator/allowlist.toml`
  with a comment. Prefer `decide`/`Decidable` over exact rationals, as
  `checkPDq` does. *Practical note from session 1:* kernel `decide` does **not**
  reduce `ℚ` arithmetic (it gets stuck on `Rat.num`), so concrete instances are
  discharged by `simp`/`norm_num` instead — see MEMORY.
* **Faithful-or-wipe.** Never silently weaken a statement. An honest labelled
  `sorry` in a clearly-reported lemma is acceptable; a fake theorem is not. **A
  bound that degenerates to something trivially true (e.g. `0 ≤ …`) is a fake
  theorem — say so and restate.** `Cond.distGE_zero_vacuous` exists precisely
  to make this checkable.
* **Edit ONLY files under `Conditioning/`.** Never `Challenge.lean`,
  `STATEMENTS.md`, `comparator/*`, `lakefile.toml`, or another tier. Headline
  statements are **proposals**, written to
  `Conditioning/CHALLENGE-COND.proposed.lean` (+ `.md`) and
  `Conditioning/COMPARATOR-ROWS.md`; the orchestrator merges and commits.
* **Do not run git commands.** The orchestrator commits.
* `/workspace/certified-positivity` is **FROZEN, read-only, never edit**. It is
  the template (`gershgorin_margin`, `coverage_band`, `checkPDq_sound`,
  `three_grid_last_row_gershgorin_zero`); its pin is v4.28.0 vs our v4.32.0, so
  **schema-level adaptation only, never import**.

## Build discipline

```
export PATH="$HOME/.elan/bin:$PATH"
lake env lean Conditioning/<Module>.lean
```

`lakefile.toml` has **no `Conditioning` library yet** (orchestrator action
requested in `COMPARATOR-ROWS.md`). Until it does, install `.olean`s by hand so
that intra-tier imports resolve — `.lake/build/lib/lean` is already on
`LEAN_PATH` under `lake env`:

```
lake env lean Conditioning/M.lean -o .lake/build/lib/lean/Conditioning/M.olean \
                                  -i .lake/build/lib/lean/Conditioning/M.ilean
```

Keep at most **one** long elaboration running (a sibling agent shares the
machine).

## Module map

| module | contents |
|--------|----------|
| `Defs.lean` | `sqNorm`, `quadForm`, `SigmaSing`, `SpecNormLe`, `SigmaMinGE`, `DistGE`, `IsEigenvalue`, `quadForm_gram` |
| `Gershgorin.lean` | `gershRadius`, `gershgorin_rayleigh_floor`, `gershgorin_disc` |
| `Margin.lean` | Gram transport, distance theorem, eigenvalue margin, `distGE_zero_vacuous`, `κ` bound, `solve_error_bound` |
| `Checker.lean` | `toReal`, `gramQ`, `gershRadiusQ`, `condCheck` + soundness suite, `discCheck`, Levy–Desplanques |
| `Bridge.lean` | `euc`, ℓ² operator norm, `Metric.infDist`, Mathlib Hermitian eigenvalues |
| `Sharpness.lean` | the three witnesses |

## Aristotle

Free to use, no permission needed. `python3 scripts/aristotle.py submit --dir
<fresh-dir> --prompt "..."` with a SMALL standalone `Main.lean` (import
Mathlib + minimal defs + one sorry'd lemma); poll `status --id <id>` at ≥ 90 s;
`fetch --id <id> --dest <dir>`; then **re-verify locally** — output is
UNTRUSTED until it compiles here and passes `#print axioms`. Submit hard
obligations early and keep local work in flight; do not idle waiting. Record
every job id + verdict in MEMORY. (Note: the helper warns that Aristotle
prefers toolchain v4.28.0 while we pin v4.32.0.)

## Open work / next targets

* **Climb the wall.** Witness 2 certifies that Gershgorin reads exactly `0` on
  a well-posed input. An exact-`ℚ` Cholesky/Sylvester engine on the Gram matrix
  would certify a positive margin there and would make the wall witness a
  *motivated* result rather than only a cautionary one. The frozen
  `checkPDq` is the obvious schema.
* **Perturbed-`A` forward error**: `‖x-y‖ ≤ (‖E‖‖x‖+ε)/(c-‖E‖)`. Needs a
  triangle inequality for a vector norm; `Bridge.euc` + `norm_add_le` is the
  route.
* **A second `Σ`**: polynomials with a repeated root, `Σ = {p | disc p = 0}`,
  with an exact-`ℚ` discriminant checker. This would make "conditioning" a
  *pattern* in this repo rather than one instance.
* **`n`-dimensional sharpness family**: generalize witness 1 from `Fin 2` to
  arbitrary diagonal rational matrices — `condCheck` output `= min|dᵢ|` `=`
  distance, for all `n`.
* **Upper bound on `‖A‖`** over `ℚ` (Frobenius is easy), to turn
  `specNormLe_inv_of_sigmaMinGE` into a fully executable certified
  `κ₂(A) ≤ N/c`.

## MEMORY (append-only, dated)

* 2026-07-27 — Tier initialized. Read `SWEEP.md` (S1/S2 binding), root
  `AGENTS.md`, `Challenge.lean`, `STATEMENTS.md`, and the frozen
  `certified-positivity` templates (`R5Prime.lean` `gershgorin_margin` /
  `coverage_band`, `R_B1.lean` `checkPDq_sound`, `R5Final.lean`
  `three_grid_last_row_gershgorin_zero`, `config-comparator-strict.json`).
  **Design decision taken at the outset:** route everything through
  `σ_min(A) ≥ c`, obtained by applying the (symmetric-only) Gershgorin engine
  to the **exact rational Gram matrix `AᵀA`**. This (a) covers arbitrary square
  matrices, not just symmetric ones; (b) makes the distance theorem
  `dist(A,Σ) ≥ σ_min(A)` a four-line contradiction argument; (c) **avoids
  needing Eckart–Young entirely**, which matters because S1 says it is already
  formalized elsewhere.
* 2026-07-27 — Aristotle job `e4845445-04c7-4e04-80c9-5a23dc47dac7` submitted
  (standalone `gershgorin_rayleigh_floor`). **Verdict: SUPERSEDED** — proved
  locally before the job returned; still `RUNNING` at session end, nothing
  fetched, nothing trusted, no output used. Helper warns Aristotle prefers
  toolchain v4.28.0 vs our v4.32.0.
* 2026-07-27 — `Defs.lean` landed. API notes for successors: `Matrix.mulVec`
  is in namespace `Matrix` but **`dotProduct` is at root** — `simp only
  [Matrix.mulVec, dotProduct]`, and `Matrix.dotProduct` does not exist. Triple
  sums reorder with `Finset.sum_comm` applied inner-first via `simp_rw`.
* 2026-07-27 — `Gershgorin.lean` landed, **both** forms proved from scratch
  (Mathlib has no Gershgorin at v4.32.0). The Rayleigh floor's only real trick
  is the symmetrization swap `∑ᵢ∑_{j≠i}|Mᵢⱼ|xⱼ² = ∑ᵢ∑_{j≠i}|Mᵢⱼ|xᵢ²`, done by
  rewriting `erase`-sums as `if`-sums (`Finset.filter_ne'` + `Finset.sum_filter`)
  and applying `Finset.sum_comm`. The pointwise bound wants the explicit SOS
  certificate `|m|(a²+b²)/2 + mab = [(|m|+m)(a+b)² + (|m|−m)(a−b)²]/4` fed to
  `nlinarith` — bare `nlinarith` does not find it. The circle theorem is the
  maximal-coordinate argument and is short.
* 2026-07-27 — `Margin.lean` landed. `nlinarith` repeatedly failed on
  `c² ≤ b², 0 ≤ b < c ⊢ False`-shaped goals; the fix each time is to supply
  `le_of_mul_le_mul_right` explicitly and hand it the factored product
  `0 < (c-b)*(c+b)`. Added `distGE_zero_vacuous` as a *first-class honesty
  lemma*: it proves that a zero certificate is content-free, which is what lets
  the wall witness be stated without overclaiming.
* 2026-07-27 — `Checker.lean` landed (`condCheck` + 6 soundness corollaries,
  `discCheck`, Levy–Desplanques). Cast lemmas done **entrywise** (`ext i j;
  push_cast`) rather than via `Matrix.map_mul`, which needs the function to be
  syntactically `⇑f` for a `RingHom` and is brittle.
* 2026-07-27 — **IMPORTANT PRACTICAL FINDING.** Kernel `decide` does **not**
  evaluate `ℚ` arithmetic: `by decide` on `condCheck A c = true` for a concrete
  rational matrix gets stuck reducing `Rat.num` (`Rat.add`/`Rat.normalize` go
  through `Nat.gcd`, which the kernel will not unfold). This is why
  `certified-positivity` never evaluates `checkPDq` on a concrete input. The
  working substitute, used throughout `Sharpness.lean`, is
  `rw [condCheck_eq_true]` then `fin_cases i <;> simp [gershRadiusQ_eq, gramQ,
  <matrix>, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num`, with the helper
  `gershRadiusQ_eq : gershRadiusQ M i = (∑ j, |M i j|) - |M i i|`
  (`Finset.sum_erase_eq_sub`) to get rid of the `erase`. **No `native_decide`
  was needed and none is used.**
* 2026-07-27 — `Sharpness.lean` landed: all three witnesses proved. Witness 1
  `!![3,0;0,5]` (floor = distance = 3 exactly, upper bound by explicit
  perturbation `!![-3,0;0,0]`); witness 2 `!![1,1;0,1]` (Gram `!![1,1;1,2]`,
  first-row margin **exactly 0**, checker forced to `c = 0`, yet `dist ≥ 1/2`
  certified by a direct Rayleigh argument with SOS hint
  `sq_nonneg (3v₀+4v₁)`); witness 3 `!![1,1;1,1]` (genuinely singular, no
  positive certificate possible).
* 2026-07-27 — `Bridge.lean` landed. This is the answer to "is your distance
  really a distance?": `condCheck_le_infDist` certifies a lower bound on
  Mathlib's own `Metric.infDist` in Mathlib's own ℓ² operator norm, and
  `condCheck_hermitian_eigenvalue_margin` is wired to Mathlib's own
  `Matrix.IsHermitian.eigenvalues`. Footgun confirmed and contained: the ℓ²
  operator norm is `scoped[Matrix.Norms.L2Operator]`, opened only here and in
  one `section` of the proposed Challenge block. Useful names:
  `Matrix.l2_opNorm_mulVec`, `Metric.le_infDist`,
  `Matrix.IsHermitian.mulVec_eigenvectorBasis`, `WithLp.ofLp_eq_zero`.
  `pow_le_pow_left` no longer exists — use `nlinarith` or `pow_le_pow_left₀`.
* 2026-07-27 — Deliverables written: `CHALLENGE-COND.proposed.lean`
  (**compiles**, six `:= sorry` headlines), `CHALLENGE-COND.proposed.md`
  (per-headline justification + vacuity register + proposed `STATEMENTS.md`
  changelog), `COMPARATOR-ROWS.md` (six `headlines.toml` rows, `AxiomCheck.lean`
  additions, the required `lakefile.toml` entry and its glob caveat),
  `TIER-STATUS.md`. Comparator `isDefEq` hand-run: **all six pairs match**.
  `#print axioms`: default triple on all six solutions and 20 supporting
  lemmas. No `sorry`, no `Float`, no `native_decide` anywhere in the tier.
  Only blocker: `lakefile.toml` needs a `Conditioning` library entry.
