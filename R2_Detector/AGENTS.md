# R2 agent — detector interface

Persistent charter + memory for the R2 tier agent. Read this fully at session
start; append to MEMORY after every significant step. Obey the root
`AGENTS.md` policies.

## Mission

1. **FREEZE-1 (hour-one blocker, gates R1/R3 instantiation):** commit the
   frozen `DiscoveryKernel` signature (`R2_Detector/Defs.lean`). Adapt the
   directive's reference shape minimally, then STOP DESIGNING.
2. After freeze: a minimal lemma library — composition of kernels
   (precomposition along `State' → State`), restriction (to a subtype of
   states) — and one paper-thin toy instance (finite rational list; drop =
   first exact zero found) proving inhabitability
   (`discovery_kernel_inhabited`). Nothing clever.

Deliverable: interface + toy instance green; `discovery_kernel_inhabited`
solution registered in `comparator/headlines.toml`.

## Signature freeze protocol

The signature is FROZEN once FREEZE-1 is announced in this file's MEMORY.
Any agent needing a change halts and files `R2_Detector/CHANGE-REQUESTS.md`;
the orchestrator pauses all agents, arbitrates, rebroadcasts. Expect zero or
one such event; more means the signature was wrong — stop and reconsider.

## MEMORY (append-only, dated)

* 2026-07-27 — Tier initialized at FREEZE-0 with the candidate signature in
  `Defs.lean` (generic / genuine / drop / license, `genuine` as a field
  relating Output to State). FREEZE-1 not yet declared.
* 2026-07-27 — **FREEZE-1 DECLARED.** The `DiscoveryKernel` signature in
  `Defs.lean` (fields `generic`, `genuine`, `drop`, `license`) is FROZEN as
  committed at FREEZE-0 and compiles green. R1/R3 instantiation work is
  unblocked. Changes only via CHANGE-REQUESTS.md.
* 2026-07-27 — Lemmas.lean landed green (first elaboration): `comap`
  (pullback along `State' → State`, license transported verbatim), simp
  lemmas for its three data fields, `comap_id` / `comap_comap` (both `rfl`
  by structure+function eta), `restrict P := comap Subtype.val`, and
  `mapOutput g` with existential transported genuineness
  (`∃ o, g o = o' ∧ genuine o s` — needs no injectivity for the license;
  for injective `g` this IS the transport along the injection). Stopped
  there per charter ("nothing clever"). No Aristotle jobs needed.
* 2026-07-27 — Toy.lean landed green (first elaboration): `zeroDetector` on
  `State := List ℚ`, `Output := ℕ`; `drop := List.findIdx? (· == 0)`,
  `generic s := (0:ℚ) ∉ s`, `genuine i s := s[i]? = some 0`. License via
  core `List.findIdx?_eq_some_iff_getElem` + `List.getElem_mem` +
  `List.getElem?_eq_getElem` (current getElem-style API; `List.get?` is
  deprecated). Headline solution
  `DiscoveryKernels.R2.discovery_kernel_inhabited := ⟨zeroDetector⟩`.
* 2026-07-27 — Milestone `lake build R2_Detector` green (zero sorries).
  Local checks passed: def-eq `example` against the verbatim Challenge
  statement type; `#print axioms` = [propext, Classical.choice, Quot.sound]
  for the headline (default allowlist, no extension needed); concrete
  `drop [1, 0, 3] = some 1` sanity check (scratchpad only). Comparator row
  proposed in COMPARATOR-ROWS.md (solution =
  `DiscoveryKernels.R2.discovery_kernel_inhabited`, module =
  `R2_Detector.Toy`). Frozen Defs.lean NOT touched. Tier deliverable done
  pending orchestrator's comparator registration.
