/-
Copyright (c) 2026 discovery-kernels contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.

R2 — the paper-thin toy instance: the zero detector on finite rational lists.

`State := List ℚ`, `Output := ℕ`. The detector reports the index of the
first exact zero entry (`List.findIdx?`); a state is generic when it carries
no zero entry; a report `i` is genuine when the list really has `0` at index
`i`. This witnesses `discovery_kernel_inhabited` (Challenge.lean, R2
section). Scaffolding, not a contribution (see STATEMENTS.md).
-/
import R2_Detector.Defs

namespace DiscoveryKernels.R2

/-- The zero detector on finite rational lists: report the index of the
first exact zero entry, if any. Its license is sound by the specification
of `List.findIdx?`. -/
def zeroDetector : DiscoveryKernel (List ℚ) ℕ where
  generic s := (0 : ℚ) ∉ s
  genuine i s := s[i]? = some 0
  drop s := s.findIdx? (· == 0)
  license := by
    intro s i h
    obtain ⟨hi, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.mp h
    have hs : s[i] = 0 := by simpa using hp
    refine ⟨fun hgen => hgen (hs ▸ List.getElem_mem hi), ?_⟩
    rw [List.getElem?_eq_getElem hi, hs]

/-- **Inhabitability of the interface.** There is a discovery kernel on a
nontrivial state space whose license is sound; witnessed by the paper-thin
toy instance `zeroDetector` (drop = an exact zero found in a finite rational
list). Solution to the R2 headline in Challenge.lean. -/
theorem discovery_kernel_inhabited :
    Nonempty (DiscoveryKernel (List ℚ) ℕ) :=
  ⟨zeroDetector⟩

end DiscoveryKernels.R2
