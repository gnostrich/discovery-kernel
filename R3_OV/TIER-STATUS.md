# TIER-STATUS — R3 — operator-valued license (statements only)

* Proven: nothing, by design (statements-only tier; `sorry` is the correct
  final state for the headlines).
* Sorry: Challenge.lean R3 headlines (FREEZE-0 text, untouched) and the two
  proposed refined headlines below.
* Delivered: `VOCAB.md` (Mathlib v4.32 survey: exists / must-define /
  out-of-scope); `Vocab.lean` (refined definitional layer, compiles clean);
  `CHALLENGE-R3.proposed.lean` (compiles, exactly two `sorry` warnings);
  `CHALLENGE-R3.proposed.md` (analysis). `lake build R3_OV` and
  `lake build Challenge` green.
* Blocked: merge of the proposals — intentionally, on the human-review gate
  below.

## PENDING HUMAN REVIEW

The following two statements are PROPOSALS ONLY (R3 charter hard gate). The
orchestrator holds the merge until the operator approves. Full justification,
the argument that the FREEZE-0 `ov_license` iff-chain is FALSE without
positivity (counterexamples `cos nθ` over ℝ, Jordan blocks over ℂ) plus the
Noetherian gap in the FREEZE-0 rank definition, soundness checks of the easy
directions, and known residual risks: `CHALLENGE-R3.proposed.md`.
Definitions cited: `R3_OV/Vocab.lean` (extends, does not alter, FREEZE-0
`Defs.lean`; the live Challenge.lean semantics are unchanged).

### Proposed `ov_license` (MSY-shaped; replaces FREEZE-0 draft)

```lean
theorem ov_license
    {B : Type} [Ring B] [StarRing B] [PartialOrder B] [StarOrderedRing B]
    (M : ℕ → B) (hM : R3.IsOVMomentSequence B M) :
    (R3.HasFiniteOVHankelRankStable B M ↔ R3.HasFiniteRealization B M) ∧
      (R3.HasFiniteRealization B M ↔ R3.IsFinitelyAtomicOVStar B M) := sorry
```

### Proposed `ov_completeness` (free-Ax–Schanuel-shaped; replaces `True`)

```lean
theorem ov_completeness
    {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]
    {B : Type} [AddCommGroup B] [Module ℂ B]
    (E : A →ₗ[ℂ] B) {d : ℕ} (x : Fin d → A) (n : ℕ)
    (hsa : ∀ i, star (x i) = x i)
    (hfaith : ∀ a : A, E (star a * a) = 0 → a = 0)
    (halign : R3.HasOVAlignment E x n) :
    R3.HasPolyCause x n := sorry
```

Reviewer decision points (details in the .md): (1) strengthen `OVHankelPSD`
to complete positivity? (2) restrict `B` to a C*-algebra in `ov_license`'s
second chain? (3) allow atoms in matrix amplifications `Mₙ(B)`? (4) keep
scalar (ℂ) alignment coefficients or demand the `B`-valued amalgamated form?
