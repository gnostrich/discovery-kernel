# CHALLENGE-COND.proposed.md — justification for the Conditioning headlines

Prepared 2026-07-27 by the Conditioning tier agent. The Lean source of these
statements is `Conditioning/CHALLENGE-COND.proposed.lean`, which **compiles**
(`lake env lean Conditioning/CHALLENGE-COND.proposed.lean`, six by-design
`sorry` warnings and nothing else). The orchestrator is asked to place the
block from `-- ==== COND ====` to the end of the namespace **first** in
`Challenge.lean`.

---

## What is being claimed, and what is not

`Conditioning/SWEEP.md` (S1, binding) records that **Eckart–Young–Mirsky,
Weyl, Courant–Fischer and Davis–Kahan are already formalized in Lean 4** in
`YuanheZ/lean-stat-learning-theory`. This tier therefore claims **no novelty
for the distance identity itself**, and — importantly — **does not use it**.
Every theorem below uses only the *lower* bound `dist(A, Σ) ≥ σ_min(A)`, which
is the easy direction and is proved here from scratch in four lines
(`Cond.distGE_of_sigmaMinGE`). Where an *upper* bound on the distance is
needed (sharpness), it is supplied by an explicit certified perturbation, not
by Eckart–Young.

What is claimed is the layer S1 found vacant:

1. `Σ` **framed as an ill-posed set**, with certified **lower** bounds
   `dist(x, Σ) ≥ c > 0` that license a finite-precision computation;
2. an **executable checker proven sound** for such a bound, over exact
   rationals;
3. **sharpness witnesses** — certified inputs where the bound is exactly the
   distance, and certified inputs where it degenerates to exactly zero.

Mathlib v4.32.0 has no condition number, no SVD, no Eckart–Young, no
distance-to-singularity, no Weyl/Courant–Fischer/Bauer–Fike and **no
Gershgorin** — so the engine (`Cond.gershgorin_rayleigh_floor`,
`Cond.gershgorin_disc`) is proved here from first principles.

---

## The six headlines

### 1. `cond_check_sound` — the `checkPDq_sound` shape, for conditioning

```lean
theorem cond_check_sound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (c : ℚ)
    (h : Cond.condCheck A c = true) :
    Cond.SigmaMinGE (Cond.toReal A) (c : ℝ) := sorry
```

`Cond.condCheck : Matrix (Fin n) (Fin n) ℚ → ℚ → Bool` is a `decide`-based
decision procedure over exact rationals (no `Float`, no `native_decide`),
directly modelled on `certified-positivity`'s `checkPDq` — **schema-level
adaptation, no code imported** (their pin is v4.28.0, ours is v4.32.0).

It applies the Gershgorin diagonal-dominance test to the **exact rational Gram
matrix `AᵀA`**. This Gram transport (`Cond.quadForm_gram`:
`vᵀ(AᵀA)v = ‖Av‖²`) is what makes a symmetric-only engine certify an
**arbitrary** square matrix, with no symmetry hypothesis on `A`.

`Cond.SigmaMinGE A c` is `σ_min(A) ≥ c`, written elementarily as
`c²‖v‖² ≤ ‖Av‖²`. `Cond.sigmaMinGE_iff_norm` proves this is equivalent to
`c‖v‖ ≤ ‖Av‖` in Mathlib's genuine `EuclideanSpace` norm, so the elementary
phrasing is a convenience, not a weakening.

**Soundness only.** Stated in the docstring; headline 6 certifies an input
where the checker is blind.

### 2. `cond_dist_to_illposed` — THE HEADLINE

```lean
theorem cond_dist_to_illposed {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (c : ℚ)
    (hn : 0 < n) (h : Cond.condCheck A c = true) :
    (c : ℝ) ≤ Metric.infDist (Cond.toReal A) (Cond.SigmaSing n) := sorry
```

An executable exact-rational check certifies a lower bound on a **genuine
metric distance** to the ill-posed set, using Mathlib's own `Metric.infDist`
and Mathlib's own ℓ² operator norm. This is the Condition Number Theorem's
usable direction: `κ(A) = ‖A‖ / dist(A, Σ)`, so `dist ≥ c` is `κ ≤ ‖A‖ / c`.

Two things in this statement are load-bearing and are flagged in the Lean
docstring:

* **The scoped-instance footgun.** Mathlib's ℓ² operator norm on `Matrix` is
  `scoped[Matrix.Norms.L2Operator]` and is *not* the default `Matrix` norm.
  Without the `open scoped`, `Metric.infDist` here would silently mean a
  different norm — the statement would still typecheck and would be a
  different theorem. The proposal therefore wraps this single declaration in
  `section L2OperatorNormScope ... end`, so the scope cannot leak into any
  other statement in `Challenge.lean`. **Do not hoist the `open` to the top of
  the file and do not delete it.**
* **`0 < n`.** For `n = 0` the empty matrix has `det = 1`, so `Σ = ∅` and
  `Metric.infDist _ ∅ = 0`; the theorem would be false. This is a genuine
  hypothesis, not decoration.

### 3. `cond_licenses_computation` — the tier's point

```lean
theorem cond_licenses_computation {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (c : ℚ)
    (h : Cond.condCheck A c = true) (x y b b' : Fin n → ℝ)
    (hx : Cond.toReal A *ᵥ x = b) (hy : Cond.toReal A *ᵥ y = b') (ε : ℝ)
    (hε : Cond.sqNorm (b - b') ≤ ε ^ 2) :
    (c : ℝ) ^ 2 * Cond.sqNorm (x - y) ≤ ε ^ 2 := sorry
```

A margin is only worth certifying if it buys something. This is the purchase:
right-hand-side accuracy `ε` converts into solution accuracy `ε / c`. Stated
squared so that no square root — and hence no temptation toward `Float` —
appears anywhere. It is the exact analogue of R1's `pslq_empirical_sound`.

*Honest scope note.* Only the right-hand side is perturbed here, not `A`. The
`A`-perturbation version (`‖x-y‖ ≤ (‖E‖‖x‖+ε)/(c-‖E‖)`) needs the triangle
inequality on the vector norm and was not attempted; the *invertibility* half
of it — that `A + E` stays nonsingular for `‖E‖ < c` — **is** proved
(`Cond.distGE_of_sigmaMinGE`, and headline 2). Nothing is claimed that is not
proved.

### 4. `cond_eigenvalue_margin` — the charter's target shape

```lean
theorem cond_eigenvalue_margin {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (c : ℚ)
    (h : Cond.condCheck A c = true) (hA : (Cond.toReal A).IsHermitian) (j : Fin n) :
    (c : ℝ) ≤ |hA.eigenvalues j| := sorry
```

This is literally the shape the tier charter asked for —
`condCheck M c = true → ∀ eigenvalue λ, c ≤ |λ|` — wired to **Mathlib's own**
`Matrix.IsHermitian.eigenvalues`, not to a bespoke eigenvalue predicate. (The
bespoke `Cond.IsEigenvalue` exists and is more general — it covers arbitrary
square matrices — and `Cond.isEigenvalue_eigenvalues` shows Mathlib's
eigenvalues are instances of it.) For symmetric matrices, `Σ` is exactly the
matrices with a zero eigenvalue, so this *is* the distance statement, in
eigenvalue form.

### 5. `cond_margin_sharp` — sharpness witness: the floor is exact

```lean
theorem cond_margin_sharp :
    Cond.condCheck Cond.diagA 3 = true ∧
      Cond.DistGE (Cond.toReal Cond.diagA) 3 ∧
      (∀ c : ℝ, 3 < c → ¬ Cond.DistGE (Cond.toReal Cond.diagA) c) ∧
      (∀ c : ℚ, Cond.condCheck Cond.diagA c = true → c ≤ 3) := sorry
```

`Cond.diagA = !![3,0;0,5]`. All four conjuncts together say: **the engine's
output on this input is exactly `3`, and `3` is exactly `dist(diagA, Σ)`.**
The lower bound comes from the executable check; the upper bound comes from an
explicit perturbation `!![-3,0;0,0]` of certified spectral norm `3` that lands
in `Σ`. No Eckart–Young, no SVD: the tightness is witnessed, not deduced.

This is what distinguishes a certified floor from a conservative one.

### 6. `cond_gershgorin_wall` — sharpness witness: the floor degenerates

```lean
theorem cond_gershgorin_wall :
    Cond.gramQ Cond.wallA 0 0 - Cond.gershRadiusQ (Cond.gramQ Cond.wallA) 0 = 0 ∧
      (∀ c : ℚ, Cond.condCheck Cond.wallA c = true → c = 0) ∧
      Cond.DistGE (Cond.toReal Cond.wallA) (1 / 2) := sorry
```

`Cond.wallA = !![1,1;0,1]`, a unimodular shear with `det = 1`. Its exact
rational Gram matrix is `!![1,1;1,2]`, whose first row has diagonal-dominance
margin **exactly zero** — an *equality between exact rationals*, so no sharper
enclosure of the entries can change it. The Gershgorin engine therefore
certifies only `c = 0` on this input, and by `Cond.distGE_zero_vacuous`
(`DistGE A 0` holds for **every** matrix, singular ones included) that output
is vacuous. Yet the third conjunct certifies `dist(wallA, Σ) ≥ 1/2 > 0` by a
direct Rayleigh argument.

So the reported zero is a property of the **engine**, not of the input. The
companion `Cond.singular_dist_zero` certifies the opposite case — an input
(`!![1,1;1,1]`) where the truth really is zero and no positive certificate can
exist. Having both is what makes a reported floor interpretable at all.

This is the conditioning analogue of `certified-positivity`'s
`three_grid_last_row_gershgorin_zero`, and it is deliberately stated as a
headline rather than buried: an engine's wall is a first-class result.

---

## Where the honest answer is "this would be vacuous"

Recorded here so that nothing in the prose overstates the Lean:

* **`DistGE A 0` is vacuously true for every matrix.** Proved as
  `Cond.distGE_zero_vacuous`. Any `c = 0` certificate is therefore a fake
  theorem if presented as a bound. Headline 6 is the certified instance of
  this happening.
* **`Cond.gershgorin_rayleigh_floor` makes no sign assumption on `μ`.** For
  `μ ≤ 0` its conclusion is true but says nothing. This matches the frozen
  prior art (`R5.gershgorin_margin`) and is stated in the docstring.
* **`Cond.discCheck` is deliberately *not* wired to `DistGE`.** It bounds the
  **real** eigenvalues of `A` and certifies nonsingularity, but for a
  non-normal matrix an eigenvalue margin is not a distance to singularity, and
  a real matrix may have no real eigenvalues at all. Claiming a distance from
  it would be a fake theorem; the docstring says so.
* **Completeness is never claimed**, for either checker, anywhere.

## STATEMENTS.md changelog paragraph (proposed text)

> * 2026-07-27 — **CONDITIONING tier added** (headline claim). Six statements
>   land in a new leading `-- ==== COND ====` section of `Challenge.lean`:
>   `cond_check_sound`, `cond_dist_to_illposed`, `cond_licenses_computation`,
>   `cond_eigenvalue_margin`, `cond_margin_sharp`, `cond_gershgorin_wall`. All
>   six are **proved** in `Conditioning/` (sorry-free, axioms exactly
>   `[propext, Classical.choice, Quot.sound]`). The organizing identity is the
>   Condition Number Theorem `κ(x) = ‖x‖ / dist(x, Σ)` (Demmel 1987;
>   Bürgisser–Cucker 2013). Per `Conditioning/SWEEP.md` S1 this repository
>   claims **no novelty for Eckart–Young–Mirsky, Weyl, Courant–Fischer or
>   Davis–Kahan** — all four are already formalized in Lean 4 in the
>   third-party `YuanheZ/lean-stat-learning-theory` — and does not use them:
>   only the elementary lower bound `dist(A, Σ) ≥ σ_min(A)` is used, proved
>   here from scratch. What is claimed is the certified **executable**
>   exact-rational lower bound on `dist(x, Σ)` and the **sharpness witnesses**
>   (`cond_margin_sharp`, `cond_gershgorin_wall`) certifying where the bound is
>   exact and where it degenerates to exactly zero. `cond_dist_to_illposed` is
>   stated in Mathlib's ℓ² operator norm, whose instance is
>   `scoped[Matrix.Norms.L2Operator]`; the statement carries its own `section`
>   opening that scope and the scope must not be hoisted.
