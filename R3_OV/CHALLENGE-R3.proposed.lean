/-
Copyright (c) 2026 discovery-kernels contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.

# CHALLENGE-R3.proposed.lean — PROPOSED refined R3 headlines

PENDING HUMAN REVIEW — this file is a PROPOSAL, not the statement registry.
Challenge.lean's R3 section is untouched; per the R3 charter's human-review
gate, the orchestrator holds the merge until the operator approves. Upon
approval, the two theorem statements below replace the bodies of
`DiscoveryKernels.Challenge.ov_license` / `ov_completeness` verbatim (the
namespace here exists only to avoid clashing with the live registry), and
the definitions they cite (R3_OV/Vocab.lean) become part of the R3
definitional layer, with a dated STATEMENTS.md changelog entry.

Justification and the analysis of why FREEZE-0's `ov_license` draft is not
kept as-is: R3_OV/CHALLENGE-R3.proposed.md.

Both statements end in `sorry` BY DESIGN: R3 is a statements-only tier.
-/
import R3_OV.Vocab

namespace DiscoveryKernels.Challenge.ProposedR3

/-- **Operator-valued license (MSY-shaped), stated frontier — PROPOSED.**
Let `B` be a star-ordered ring and `M : ℕ → B` an operator-valued moment
sequence (hermitian entries, positive semidefinite `B`-valued Hankel kernel —
the algebraic shadow of `M n = E_B (xⁿ)` for `x` self-adjoint, cf.
Mai–Speicher–Yin). Then the license chain holds:

1. finite OV Hankel rank (membership in a finitely generated shift-stable
   left `B`-submodule, Fliess/Schützenberger form) ⟺ finite linear
   realization over `B` (rational `B`-valued resolvent); and
2. finite linear realization ⟺ finitely atomic in the star sense
   (`M n = ∑ i, star (w i) * (a i)ⁿ * w i`, self-adjoint atoms `a i ∈ B`,
   manifestly positive weights).

Chain 1 is theorem-shaped over every ring and needs neither star, order, nor
`hM`. Chain 2 is the MSY frontier: the moment hypothesis `hM` is essential —
without positivity the FREEZE-0 unconditional version is FALSE (Jordan
blocks / `cos nθ`-type realizations have no atomic form; see the proposal
notes). For `B = ℂ` chain 2 is classical (finite-rank PSD Hankel ⟺ finitely
atomic Hamburger measure); for general `B` it is stated frontier. `sorry` BY
DESIGN. -/
theorem ov_license
    {B : Type} [Ring B] [StarRing B] [PartialOrder B] [StarOrderedRing B]
    (M : ℕ → B) (hM : R3.IsOVMomentSequence B M) :
    (R3.HasFiniteOVHankelRankStable B M ↔ R3.HasFiniteRealization B M) ∧
      (R3.HasFiniteRealization B M ↔ R3.IsFinitelyAtomicOVStar B M) := sorry

/-- **Operator-valued completeness (free-Ax–Schanuel-shaped), stated
frontier — PROPOSED.** Every genuine operator-valued alignment has a
structural cause. Concretely: let `x : Fin d → A` be a self-adjoint tuple in
a complex star algebra, conditioned by a ℂ-linear map `E : A →ₗ[ℂ] B`. The
genericity/freeness hypothesis is `hfaith`: `E` is faithful on positives
(`E (star a * a) = 0 → a = 0`) — the abstract role played by a faithful
(normal) conditional expectation `E_B` in the free-probability setting
(Mai–Speicher–Weber regularity line). If the word-indexed OV moment/Hankel
data of `x` under `E` shows a rank drop at level `n` (an *alignment*: some
nonzero scalar row combination of `{E (x_{w ·}) : |w| ≤ n}` vanishes
identically), then there is a *structural cause*: a nonzero noncommutative
polynomial of degree ≤ `n` in `FreeAlgebra ℂ (Fin d)` annihilating the tuple
under evaluation. The alignment is never a numerical accident: it certifies
an exact algebraic relation. `sorry` BY DESIGN. -/
theorem ov_completeness
    {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]
    {B : Type} [AddCommGroup B] [Module ℂ B]
    (E : A →ₗ[ℂ] B) {d : ℕ} (x : Fin d → A) (n : ℕ)
    (hsa : ∀ i, star (x i) = x i)
    (hfaith : ∀ a : A, E (star a * a) = 0 → a = 0)
    (halign : R3.HasOVAlignment E x n) :
    R3.HasPolyCause x n := sorry

end DiscoveryKernels.Challenge.ProposedR3
