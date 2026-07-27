/-
Copyright (c) 2026 discovery-kernels contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.

R2 — minimal lemma library on `DiscoveryKernel`.

Deliberately small ("nothing clever"): pullback along a map of state spaces
(`comap`), restriction to a subtype of states (`restrict`), and pushforward
along a map of output types (`mapOutput`). The `DiscoveryKernel` signature
itself lives in `R2_Detector/Defs.lean` and is FROZEN at FREEZE-1; this file
only ADDS definitions and lemmas on top of it.
-/
import R2_Detector.Defs

namespace DiscoveryKernels

namespace DiscoveryKernel

variable {State State' State'' : Type*} {Output Output' : Type*}

/-! ### Pullback along a map of state spaces -/

/-- Pull a discovery kernel back along `f : State' → State`: observe through
`f` and run the original detector. The license transports verbatim. -/
def comap (K : DiscoveryKernel State Output) (f : State' → State) :
    DiscoveryKernel State' Output where
  generic s' := K.generic (f s')
  genuine o s' := K.genuine o (f s')
  drop s' := K.drop (f s')
  license s' o h := K.license (f s') o h

@[simp] theorem comap_generic (K : DiscoveryKernel State Output)
    (f : State' → State) (s' : State') :
    (K.comap f).generic s' ↔ K.generic (f s') := Iff.rfl

@[simp] theorem comap_genuine (K : DiscoveryKernel State Output)
    (f : State' → State) (o : Output) (s' : State') :
    (K.comap f).genuine o s' ↔ K.genuine o (f s') := Iff.rfl

@[simp] theorem comap_drop (K : DiscoveryKernel State Output)
    (f : State' → State) (s' : State') :
    (K.comap f).drop s' = K.drop (f s') := rfl

@[simp] theorem comap_id (K : DiscoveryKernel State Output) :
    K.comap id = K := rfl

theorem comap_comap (K : DiscoveryKernel State Output)
    (f : State' → State) (g : State'' → State') :
    (K.comap f).comap g = K.comap (f ∘ g) := rfl

/-! ### Restriction to a subtype of states -/

/-- Restrict a discovery kernel to the subtype of states satisfying `P`.
This is pullback along the inclusion `Subtype.val`. -/
def restrict (K : DiscoveryKernel State Output) (P : State → Prop) :
    DiscoveryKernel {s // P s} Output :=
  K.comap Subtype.val

@[simp] theorem restrict_generic (K : DiscoveryKernel State Output)
    (P : State → Prop) (s : {s // P s}) :
    (K.restrict P).generic s ↔ K.generic s.val := Iff.rfl

@[simp] theorem restrict_genuine (K : DiscoveryKernel State Output)
    (P : State → Prop) (o : Output) (s : {s // P s}) :
    (K.restrict P).genuine o s ↔ K.genuine o s.val := Iff.rfl

@[simp] theorem restrict_drop (K : DiscoveryKernel State Output)
    (P : State → Prop) (s : {s // P s}) :
    (K.restrict P).drop s = K.drop s.val := rfl

/-! ### Pushforward along a map of output types -/

/-- Push a discovery kernel forward along `g : Output → Output'`.
Genuineness of a transported report `o'` means: some `g`-preimage of `o'`
is genuine for the state. With that reading the license transports with no
injectivity hypothesis on `g` (for injective `g` the preimage is unique, so
this is the transported genuineness along the injection). -/
def mapOutput (K : DiscoveryKernel State Output) (g : Output → Output') :
    DiscoveryKernel State Output' where
  generic := K.generic
  genuine o' s := ∃ o, g o = o' ∧ K.genuine o s
  drop s := (K.drop s).map g
  license s o' h := by
    obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨hng, hgen⟩ := K.license s o ho
    exact ⟨hng, o, rfl, hgen⟩

@[simp] theorem mapOutput_generic (K : DiscoveryKernel State Output)
    (g : Output → Output') (s : State) :
    (K.mapOutput g).generic s ↔ K.generic s := Iff.rfl

@[simp] theorem mapOutput_genuine (K : DiscoveryKernel State Output)
    (g : Output → Output') (o' : Output') (s : State) :
    (K.mapOutput g).genuine o' s ↔ ∃ o, g o = o' ∧ K.genuine o s := Iff.rfl

@[simp] theorem mapOutput_drop (K : DiscoveryKernel State Output)
    (g : Output → Output') (s : State) :
    (K.mapOutput g).drop s = (K.drop s).map g := rfl

end DiscoveryKernel

end DiscoveryKernels
