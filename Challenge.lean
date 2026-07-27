/-
Copyright (c) 2026 discovery-kernels contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.

# Challenge.lean — the statement registry of `discovery-kernels`

This file IS the set of claims of this repository. Prose (README,
STATEMENTS.md) never claims anything this file does not state.

Rules of this file:
* Four append-only tier sections, delimited below. No agent edits another
  tier's section.
* Every headline here is stated with `:= sorry` — permanently. Solutions live
  in the tier directories and are checked against these statements by
  `comparator/` (definitional-equality check + per-theorem axiom allowlist).
  R3 headlines are stated frontier: no solution is claimed, by design.
* Statement changes after FREEZE-0 are recorded in STATEMENTS.md with a dated
  note.
-/
import R0_Kronecker.Defs
import R1_PSLQ.Defs
import R2_Detector.Defs
import R3_OV.Defs

namespace DiscoveryKernels.Challenge

-- ==== R0 ==== scalar license (Kronecker 1881) =============================

/-- **Kronecker's theorem, rank half.** A sequence over a field has finite
Hankel rank iff its generating function is rational. Kronecker (1881); Peller,
*Hankel Operators*, Ch. 1. -/
theorem hankel_finite_rank_iff_rational
    {K : Type} [Field K] (a : ℕ → K) :
    R0.HasFiniteHankelRank K a ↔ R0.IsRationalGF K a := sorry

/-- **Kronecker's theorem, atomic half.** Over an algebraically closed field of
characteristic zero, the generating function of `a` is rational iff `a` is
finitely atomic (exponential-polynomial normal form, atoms with multiplicity
= partial fractions / characteristic roots of a linear recurrence). -/
theorem rational_iff_finitely_many_atoms
    {K : Type} [Field K] [IsAlgClosed K] [CharZero K] (a : ℕ → K) :
    R0.IsRationalGF K a ↔ R0.IsFinitelyAtomic K a := sorry

-- ==== R1 ==== PSLQ: exact core, termination, empirical input ==============

/-- **PSLQ partial correctness** (FREEZE-0 placeholder — will be refined to
speak about the exact-arithmetic PSLQ-class core `R1.pslq` once that
definition lands; see STATEMENTS.md changelog). Target: if the core, run on
exact rational input `x`, reports `m`, then `m` is an integer relation of
`x`. -/
theorem pslq_partial_correct : True := sorry

/-- **PSLQ termination / lower bound** (FREEZE-0 placeholder — will be refined
against `R1.pslq` once it lands; see STATEMENTS.md changelog). Target
(Borwein–Lisoněk form): while no relation has been reported, every integer
relation of `x` has norm exceeding an explicit bound computed from the
algorithm's (rational, CSV/HJLS-normalized) Gram–Schmidt data. -/
theorem pslq_lower_bound : True := sorry

/-- **THE TIER'S POINT — empirical-input soundness.** Input known to precision
`p` (true vector `x : Fin n → ℝ`, computed rational approximation `xq` with
`|x i - xq i| ≤ p`), reported integer vector `m` with coefficient bound
`|m i| ≤ M` that is an exact relation of `xq` (which is what the exact
arithmetic core guarantees). Then:
1. the reported relation is `ε`-genuine for the truth with the explicit
   `ε(p, M, n) = n * M * p`: `|∑ mᵢ xᵢ| ≤ n * M * p`; and
2. under the separation hypothesis — every candidate integer vector `k` with
   `‖k‖∞ ≤ M` either annihilates `x` exactly or misses by more than
   `n * M * p` — the reported `m` is a genuine exact relation of `x`:
   the report is not a numerical artifact. -/
theorem pslq_empirical_sound
    {n : ℕ} (x : Fin n → ℝ) (xq : Fin n → ℚ) (p : ℝ) (M : ℤ)
    (m : Fin n → ℤ)
    (happ : ∀ i, |x i - (xq i : ℝ)| ≤ p)
    (hM : ∀ i, |m i| ≤ M)
    (hrel : R1.IsIntRelation xq m) :
    |∑ i, (m i : ℝ) * x i| ≤ (n : ℝ) * (M : ℝ) * p ∧
      ((∀ k : Fin n → ℤ, k ≠ 0 → (∀ i, |k i| ≤ M) →
          ∑ i, (k i : ℝ) * x i = 0 ∨ (n : ℝ) * (M : ℝ) * p < |∑ i, (k i : ℝ) * x i|) →
        R1.IsIntRelation x m) := sorry

-- ==== R2 ==== the DiscoveryKernel interface ===============================

/-- **Inhabitability of the interface.** There is a discovery kernel on a
nontrivial state space whose license is sound; witnessed by a paper-thin toy
instance (drop = an exact zero found in a finite rational list). This is
scaffolding, not a contribution (see STATEMENTS.md). -/
theorem discovery_kernel_inhabited :
    Nonempty (DiscoveryKernel (List ℚ) ℕ) := sorry

-- ==== R3 ==== operator-valued license — STATEMENTS ONLY ===================

/-- **Operator-valued license (MSY-shaped), stated frontier.** For an
operator-valued moment sequence over a ring `B`: finite OV Hankel rank,
existence of a finite linear realization (rational `B`-valued resolvent), and
finite atomicity are equivalent. Cf. Mai–Speicher–Yin. `sorry` BY DESIGN:
this tier states the frontier; no proof is claimed. FREEZE-0 draft shape —
requires operator review before any refinement is merged (see R3_OV/AGENTS.md). -/
theorem ov_license
    {B : Type} [Ring B] (M : ℕ → B) :
    (R3.HasFiniteOVHankelRank B M ↔ R3.HasFiniteRealization B M) ∧
      (R3.HasFiniteRealization B M ↔ R3.IsFinitelyAtomicOV B M) := sorry

/-- **Operator-valued completeness (free-Ax–Schanuel-shaped), stated frontier**
(FREEZE-0 placeholder — the definitional layer for "genuine OV alignment" and
"structural cause" is R3 work; the refined statement lands with it, under the
operator-review gate; see STATEMENTS.md changelog). Target: every genuine
operator-valued alignment (rank drop) has a structural cause (an exact
noncommutative algebraic relation). `sorry` BY DESIGN. -/
theorem ov_completeness : True := sorry

end DiscoveryKernels.Challenge
