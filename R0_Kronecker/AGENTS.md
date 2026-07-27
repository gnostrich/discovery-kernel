# R0 agent — scalar license (Kronecker 1881)

Persistent charter + memory for the R0 tier agent. Read this fully at session
start; append to MEMORY after every significant step. Obey the root
`AGENTS.md` policies (ownership, faithful-or-wipe, Aristotle protocol).

## Mission

Prove the two R0 headlines of `Challenge.lean`:

* `hankel_finite_rank_iff_rational` — finite Hankel rank (dimension of the
  span of shifts of `a` in `ℕ → K`) ⟺ rational generating function
  (`q · Σ aₙ Xⁿ = p` in `K⟦X⟧`, `q(0) ≠ 0`).
* `rational_iff_finitely_many_atoms` — over alg. closed, char 0: rational
  ⟺ exponential-polynomial normal form (atoms with multiplicity).

Deliverable: R0 green in CI, zero sorries in R0 headline solutions, solutions
registered in `comparator/headlines.toml` (fill `solution` + `module` rows).

## Hour-one blocker (do first)

Sweep Mathlib for: Hankel matrices, rational generating functions / power
series, linear recurrences (`Mathlib/Algebra/LinearRecurrence.lean`),
partial fractions (`Mathlib/Algebra/Polynomial/PartialFractions.lean`?),
moment problems. Write `R0_Kronecker/SWEEP.md`: one verdict per needed lemma —
BUILD / PORT / CITE(`Mathlib.X.Y.z`). If PORT/CITE, wrap and re-export rather
than re-prove; the headline must still pass the comparator.

## Proof strategy notes (from orchestrator)

* Rank → rational: the row space `V = span(shifts a)` is shift-invariant and
  finite-dimensional; the shift endomorphism `S : V → V` has a monic
  annihilating polynomial (its minimal/characteristic polynomial, via
  `Module.End` + Cayley–Hamilton or `minpoly`); applied to the vector
  `a = shiftSeq a 0 ∈ V` it yields a linear recurrence for `a`; a linear
  recurrence with char. polynomial `χ(X)` gives `q(X) = X^d·χ(1/X)` (reversed
  polynomial, `q(0) = 1 ≠ 0` for monic χ) with `q · A` a polynomial.
* Rational → rank: `q · A = p` with `q(0) ≠ 0` forces the recurrence
  `Σ q_k a_{n+d-k}`-style relation for `n` large; hence all shifts lie in the
  span of finitely many shifts plus finitely many coordinate corrections —
  bound the row space by an explicit finite spanning set.
* Atoms: use `X^d · χ(1/X)` reversal both ways; alg. closed splits `q`;
  partial fractions gives `c/(1-λX)^k` pieces whose coefficient sequences are
  `(binomial poly in n)·λⁿ`; char 0 keeps `n ↦ (n:K)^j` independent.

## MEMORY (append-only, dated)

* 2026-07-27 — Tier initialized at FREEZE-0; no proof work started yet.
