# CHALLENGE-R1.proposed.md — proposed Challenge.lean refinements (R1)

Prepared 2026-07-27 by the R1 agent. **The orchestrator applies these** — the
R1 agent does not edit `Challenge.lean` or `STATEMENTS.md`.

Both replacement statements below have been checked with the comparator's own
mechanism (`isDefEq` of the two constants' types, as in
`comparator/AxiomCheck.lean`) against the proved R1 constants. Both matched.

---

## 0. Import line Challenge.lean needs

`Challenge.lean` states these using `R1.pslq`, `R1.pslqState`,
`R1.PSLQState.coords`, `R1.PSLQState.gsoNormSq` and `R1.IsIntRelation`. All of
them live in (or are re-exported through) `PSLQ.Core`, so exactly one new
import line is required:

```lean
import PSLQ.Core        -- transitively imports PSLQ.Defs
```

*Status: already applied by the orchestrator* (Challenge.lean now reads
`import PSLQ.Defs` / `import PSLQ.Core` / `import OV.Defs`).
No import of `PSLQ.Bound` is needed by `Challenge.lean` — `Bound.lean`
supplies only the proof; the comparator imports it for the solution side.

---

## 1. `pslq_partial_correct` — ALREADY LANDED

The orchestrator already replaced the `True` placeholder with exactly the
statement below; it is recorded here for the registry's sake and because the
comparator pair is now live.

```lean
/-- **PSLQ partial correctness.** If the exact-arithmetic PSLQ-class core
`R1.pslq`, run on exact rational input `x` with any fuel, reports `m`, then
`m` is an integer relation of `x` (nonzero, with `∑ mᵢ xᵢ = 0`).

Soundness only: this says a report is correct, never that the core reports
whenever a relation exists. Refined from the FREEZE-0 `True` placeholder on
2026-07-27, when `R1.pslq` landed; see STATEMENTS.md changelog. -/
theorem pslq_partial_correct
    {n : ℕ} (x : Fin n → ℚ) (fuel : ℕ) (m : Fin n → ℤ)
    (h : R1.pslq x fuel = some m) :
    R1.IsIntRelation x m := sorry
```

Solution: `DiscoveryKernels.R1.pslq_partial_correct` (`PSLQ/Core.lean`),
proved, axioms `[propext, Classical.choice, Quot.sound]`.

---

## 2. `pslq_lower_bound` — PROPOSED REPLACEMENT (exact text)

Replace

```lean
theorem pslq_lower_bound : True := sorry
```

with

```lean
/-- **PSLQ termination / lower bound (Borwein–Lisoněk form).** While the
exact-arithmetic core has reported no relation within `fuel` rounds
(`R1.pslq x fuel = none`), every integer relation `m` of the exact rational
input `x` is large: its squared euclidean norm is at least the explicit
rational number `gsoNormSq x k` read off the state's own rational
(CSV/HJLS-normalized) Gram–Schmidt data after `fuel` rounds, where `k` is the
last index at which `m` has a nonzero coordinate in the algorithm's current
basis (`coords m = Binv · m`, an integer vector by unimodularity).

The index `k` is stated rather than hidden behind a `min` because it must be:
the `n` projections of the basis columns onto `x^⊥` span an
`(n-1)`-dimensional space, so exactly one Gram–Schmidt direction degenerates
and a `min` over all `j` would be the trivial bound `0`. Pinning `k` is what
makes the bound a real one. Refined from the FREEZE-0 `True` placeholder on
2026-07-27; see STATEMENTS.md changelog. -/
theorem pslq_lower_bound
    {n : ℕ} (x : Fin n → ℚ) (fuel : ℕ) (hnone : R1.pslq x fuel = none)
    (m : Fin n → ℤ) (hm : R1.IsIntRelation x m) (k : Fin n)
    (hk : (R1.pslqState x fuel).coords m k ≠ 0)
    (hlast : ∀ j, k < j → (R1.pslqState x fuel).coords m j = 0) :
    (R1.pslqState x fuel).gsoNormSq x k ≤ ∑ i, ((m i : ℚ)) ^ 2 := sorry
```

Solution: `DiscoveryKernels.R1.pslq_lower_bound` (`PSLQ/Bound.lean`),
proved, no `sorry`, axioms `[propext, Classical.choice, Quot.sound]`.
Comparator `isDefEq` check against this exact text: **OK**.

### Honest notes on the statement (read before applying)

1. **`hnone` is not used by the proof.** The bound holds at *every* state
   satisfying the loop invariant; `PSLQ/Bound.lean` also exposes the
   stronger hypothesis-free state-level form
   `R1.PSLQState.gsoNormSq_le_of_relation`. `hnone` is kept in the headline
   because the charter's target sentence is "*while no relation has been
   reported*, every integer relation …", and because it is what makes this the
   *relevant* state. Including it makes the headline weaker than what is
   proved, never stronger. (`R1.pslq_none_report` and
   `R1.pslq_none_y_ne_zero` in `Bound.lean` make "no relation has been
   reported" precise: no exact zero has appeared in `y`.)
2. **Why this is the Borwein–Lisoněk bound.** The classical form
   (Ferguson–Bailey–Arno 1999 Thm 1) is `‖m‖ ≥ 1 / max_j |H_{jj}|` for the
   lower-trapezoidal `H`. `H` and the primal Gram–Schmidt data `b*_j` used
   here are diagonals of mutually inverse triangular factors, which is why the
   classical form carries a reciprocal and a `max` and this one does not. The
   proof is the classical one: `m = ∑_j z_j p_j` with `z = Binv · m` integer,
   `⟨m, b*_k⟩ = z_k ‖b*_k‖²` at the top `k` of the support of `z`,
   Cauchy–Schwarz, and `z_k² ≥ 1` because `z_k` is a nonzero integer. In fact
   `‖m‖² ≥ z_k² ‖b*_k‖²` is what the proof gives; the headline states the
   `z_k² ≥ 1` consequence.
3. **Uniform-bound corollary.** `R1.PSLQState.gsoNormSq_le_of_relation_of_min`
   proves the `min`-shaped packaging (`c ≤ gsoNormSq x j` for all `j` implies
   `c ≤ ‖m‖²` for every relation `m`). It is stated but, as note 2's
   degeneracy remark explains, it is only non-vacuous for states whose GSO
   data is nondegenerate; that is why it is a corollary and not the headline.

---

## 3. STATEMENTS.md changelog entry (dated, ready to paste)

> **2026-07-27 — R1 `pslq_partial_correct` and `pslq_lower_bound` refined from
> the FREEZE-0 `True` placeholders.** The exact-arithmetic PSLQ-class core
> landed (`PSLQ/Core.lean`: `R1.pslq`, a fuel-driven detector over `ℚ` in
> the CSV/HJLS normalization — state `(y, B, Binv)` with loop invariant
> `y = x ⬝ B` and an explicit integer two-sided inverse of `B` as the
> unimodularity certificate; every mutation goes through certified elementary
> column operations, so partial correctness is independent of the search
> strategy). `pslq_partial_correct` now states soundness of the core's report:
> a reported `m` is an exact integer relation of the exact rational input.
> `pslq_lower_bound` now states the Borwein–Lisoněk termination bound over the
> state's *exact rational* Gram–Schmidt data (`PSLQ/Bound.lean`): while the
> core has reported nothing, every integer relation `m` of `x` satisfies
> `‖m‖² ≥ gsoNormSq x k`, where `k` is the last index at which `m` has a
> nonzero coordinate in the algorithm's own basis. The index `k` is part of
> the statement rather than a `min` over all indices because exactly one
> Gram–Schmidt direction necessarily degenerates (the `n` projected basis
> columns span the `(n-1)`-dimensional `x^⊥`), which would make a `min`-shaped
> bound the trivial `0`. Both statements are strengthenings of `True`; no
> previously claimed statement was weakened. Both are proved sorry-free with
> axioms `[propext, Classical.choice, Quot.sound]`. `Challenge.lean` gains
> `import PSLQ.Core` (definitional layer of the core; the proofs of both
> headlines live in `PSLQ/Core.lean` and `PSLQ/Bound.lean` and are
> pulled in only by the comparator). No `Float` and no `ℝ` occurs in the R1
> core, the bound, or either statement.
