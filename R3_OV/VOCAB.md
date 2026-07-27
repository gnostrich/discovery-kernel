# R3_OV/VOCAB.md — what Mathlib v4.32.0 actually has for the OV tier

Survey date: 2026-07-27. Method: direct grep/inspection of
`.lake/packages/mathlib/Mathlib` (the pinned Mathlib `v4.32.0`). Verdicts are
**EXISTS** (usable as-is, module path given), **MUST-DEFINE** (absent; the
minimal surrogate lives in `R3_OV/Defs.lean` / `R3_OV/Vocab.lean`), or
**OUT-OF-SCOPE** (absent and not worth building for a statements-only tier).

## 1. Von Neumann algebras — EXISTS (skeleton only)

* `VonNeumannAlgebra H` — concrete definition: a star-subalgebra of
  `H →L[ℂ] H` equal to its double commutant. Bundled structure.
  `Mathlib.Analysis.VonNeumannAlgebra.Basic` (162 lines total).
* `WStarAlgebra M` — abstract (Sakai) definition: `Prop`-class asserting a
  Banach predual exists. Same file.
* What the file itself says is missing: the double-commutant theorem
  ("We still have a major project ahead of us"). Also absent: normal states,
  weights, type classification, standard form, group von Neumann algebras,
  II₁ factors, traces on vN algebras.
* Verdict for R3: usable only as decoration; nothing to compute with. We do
  NOT state over `VonNeumannAlgebra` — the MSY setting (finite vN algebra
  with faithful normal trace) is unformalizable at reasonable cost, so its
  role is abstracted into ring/star/order hypotheses. Flagged in every
  docstring.

## 2. C*-algebras — EXISTS (substantial)

* Classes: `CStarRing` (`Mathlib.Analysis.CStarAlgebra.Basic`, line 89);
  `NonUnitalCStarAlgebra`, `CStarAlgebra`, `CommCStarAlgebra`
  (`Mathlib.Analysis.CStarAlgebra.Classes`).
* Gelfand duality: `Mathlib.Analysis.CStarAlgebra.GelfandDuality`.
* GNS construction: `Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal`.
* Continuous functional calculus (the workhorse):
  `Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.{Unital,
  NonUnital, Order, Instances, Isometric, ...}` (17 files).
* Order/positivity: `StarOrderedRing`
  (`Mathlib.Algebra.Order.Star.Basic`, line 79 — `0 ≤ x ↔ x` is a sum of
  `star s * s`); C*-order facts in `...ContinuousFunctionalCalculus.Order`.
* Completely positive maps: `Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap`.
* Hilbert C*-modules: `CStarModule`
  (`Mathlib.Analysis.CStarAlgebra.Module.Defs`, line 72) — B-valued inner
  products exist! But no interior tensor products, no Kasparov machinery.
* Matrix C*-algebras: `Mathlib.Analysis.CStarAlgebra.CStarMatrix`.
* Verdict: the *positivity language* we need (`StarRing`, `PartialOrder`,
  `StarOrderedRing`) EXISTS and is what our refined statements use. The
  analytic C*-theory itself is not needed for statements.

## 3. Conditional expectation — EXISTS but the WRONG KIND

* `MeasureTheory.condExp` (notation `μ[f|m]`) —
  `Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic` (line 102),
  plus `condExpL1`, `condExpL2` in sibling files. This is the
  measure-theoretic conditional expectation w.r.t. a sub-σ-algebra of a
  measure space. It is NOT the operator-algebraic `E_B : A → B` (Tomiyama:
  unital positive `B`-bimodule projection onto a subalgebra), and no bridge
  exists.
* Operator-algebraic conditional expectation: **MUST-DEFINE**. Our surrogate:
  an abstract ℂ-linear map `E : A →ₗ[ℂ] B` carrying explicitly named
  hypotheses (star-faithfulness `E (star a * a) = 0 → a = 0`); the
  `B`-bimodule property and complete positivity are DROPPED and flagged.

## 4. Operator-valued measures — PARTIAL

* `MeasureTheory.VectorMeasure` — σ-additive measures valued in a normed
  group: `Mathlib.MeasureTheory.VectorMeasure.Basic`. No positivity in the
  operator order, no POVMs, no spectral measures, no spectral theorem for
  operators in measure form. (Finite-dimensional spectral theorem exists:
  `Matrix.IsHermitian.spectral_theorem`, `Mathlib.Analysis.Matrix.Spectrum`;
  CFC substitutes in the C*-world.)
* Atoms of measures: only the σ-algebra/scalar notion (`MeasureTheory`
  typeclass `NoAtoms`, `Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms`);
  `Measure.dirac` exists (`Mathlib.MeasureTheory.Measure.Dirac`).
* Verdict: the `E_B`-conditioned spectral measure `μ = E_B ∘ E_x` of MSY is
  **MUST-DEFINE**; we do not build a measure at all. Atomicity is stated at
  the MOMENT level: `M n = ∑ i, star (w i) * (a i) ^ n * w i` with
  self-adjoint atoms `a i` (see `Vocab.lean`, `IsFinitelyAtomicOVStar`) —
  the moment sequence of the finitely-atomic B-valued measure
  `∑ i (star (w i) · w i)-weighted δ_{a i}` without saying "measure".

## 5. Free probability — NOTHING (as expected)

* Greps for `FreeProbability`, `freeIndep`, `free probability`, R-transform,
  semicircular: zero hits in all of Mathlib.
* No free independence, no free cumulants, no free convolution, no
  amalgamated free products of algebras (only the group-theoretic pushout
  `Mathlib.GroupTheory.PushoutI`). No free entropy / free Fisher
  information (the actual hypotheses of the Mai–Speicher–Weber/Yin
  regularity theorems).
* Verdict: **OUT-OF-SCOPE** to build. The free-probabilistic content of both
  headlines is carried by explicit hypothesis parameters (positivity,
  faithfulness) with docstrings naming the analytic object they abstract.

## 6. Noncommutative polynomials, words, series

* `FreeAlgebra R X` — EXISTS: `Mathlib.Algebra.FreeAlgebra`, with the
  universal property `FreeAlgebra.lift : (X → A) ≃ (FreeAlgebra R X →ₐ[R] A)`
  (line 369) and `FreeAlgebra.ι`. This IS the ring of noncommutative
  polynomials `ℂ⟨X₁,…,X_d⟩` used by `ov_completeness`.
* Word basis — EXISTS: `FreeAlgebra.basisFreeMonoid : Basis (FreeMonoid X) R
  (FreeAlgebra R X)` (`Mathlib.LinearAlgebra.FreeAlgebra`, line 39). This
  makes "nonzero polynomial from a nonzero word-coefficient vector"
  meaningful, hence the completeness statement non-vacuous.
* Star structure — EXISTS: `StarRing (FreeAlgebra R X)`
  (`Mathlib.Algebra.Star.Free`, line 49; star reverses words).
* Words — EXISTS: `FreeMonoid α` with `FreeMonoid.lift : (α → M) ≃
  (FreeMonoid α →* M)` (line 306) and `FreeMonoid.length` (line 164),
  `Mathlib.Algebra.FreeMonoid.Basic`.
* Rational / recognizable noncommutative series (Schützenberger 1961, Fliess
  1974), Hankel modules of series: **MUST-DEFINE** — zero hits for
  `Recognizable`, `Hankel` anywhere in Mathlib. Our
  `HasFiniteRealization` (Defs.lean) and stable-submodule rank
  (`Vocab.lean`) are exactly this minimal layer.

## 7. Hankel matrices / operators — NOTHING

* Grep `Hankel`: zero hits. R0 faces the same gap for the scalar case.
* Generic linear algebra that substitutes — EXISTS: `Submodule.FG`,
  `Module.Finite`, `Module.rank`, `Matrix.rank`, `Matrix.mulVec`,
  `dotProduct`, matrix powers. All statements are phrased through these.

## 8. Moments — scalar only

* `ProbabilityTheory.moment X p μ` — `Mathlib.Probability.Moments.Basic`
  (line 55): real-valued, measure-theoretic. No operator-valued analogue.
* OV moment sequence: **MUST-DEFINE**. Surrogate: `IsOVMomentSequence`
  (`Vocab.lean`) = hermitian entries + positive semidefinite OV Hankel
  kernel (level-1 Hamburger-type condition; complete positivity flagged as
  dropped).

## Bottom line

| Object (informal) | Verdict |
|---|---|
| C*-positivity language (`StarRing`/`StarOrderedRing`) | EXISTS — used |
| `FreeAlgebra`, `FreeMonoid`, word basis, star on free algebra | EXISTS — used |
| f.g. modules / matrix framework | EXISTS — used |
| von Neumann algebras beyond the bare definition | absent — abstracted into hypotheses |
| operator-algebraic `E_B` | MUST-DEFINE (surrogate: hypotheses on a linear map) |
| B-valued (spectral) measures, their atoms | MUST-DEFINE (surrogate: moment-level atomicity) |
| noncommutative rational/recognizable series, Hankel | MUST-DEFINE (Defs.lean + Vocab.lean) |
| free probability (independence, entropy, Fisher info) | OUT-OF-SCOPE (hypothesis parameters instead) |
