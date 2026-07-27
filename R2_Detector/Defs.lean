/-
Copyright (c) 2026 discovery-kernels contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.

R2 — the `DiscoveryKernel` interface.

This is organizing scaffolding, not a mathematical contribution (see
STATEMENTS.md, "What we do NOT claim"). The signature below is FROZEN at
FREEZE-1; changes go through R2_Detector/CHANGE-REQUESTS.md.
-/
import Mathlib

namespace DiscoveryKernels

/-- A **discovery kernel**: an abstract rank-drop / structure detector.

* `State` is the carrier of observations (e.g. a rational approximation of a
  real vector together with precision data).
* `Output` is the type of reported discoveries (e.g. an integer relation).
* `generic` is the genericity predicate: states with *no* exact structure.
  Detection events are only supposed to happen off the generic set.
* `genuine o s` says output `o` is a genuine (non-artifact) discovery for
  state `s`; each instantiation fixes its meaning (tier-local).
* `drop` is the drop observable / detector: it reports at most one discovery.
* `license` is the soundness ("license") theorem packaged with the detector:
  a report refutes genericity and is genuine. -/
structure DiscoveryKernel (State : Type*) (Output : Type*) where
  /-- Genericity predicate: `generic s` means `s` carries no exact structure. -/
  generic : State → Prop
  /-- Genuineness predicate for reported outputs, relative to a state. -/
  genuine : Output → State → Prop
  /-- The drop observable / detector. -/
  drop : State → Option Output
  /-- The license: every report refutes genericity and is genuine. -/
  license : ∀ s o, drop s = some o → ¬ generic s ∧ genuine o s

end DiscoveryKernels
