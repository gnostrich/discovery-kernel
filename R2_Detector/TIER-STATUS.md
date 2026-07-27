# TIER-STATUS — R2 — detector interface

* Proven: `discovery_kernel_inhabited` (solution
  `DiscoveryKernels.R2.discovery_kernel_inhabited` in `R2_Detector/Toy.lean`,
  witnessed by `zeroDetector`; zero sorries; axioms within default allowlist).
* Lemma library: `R2_Detector/Lemmas.lean` green — `comap` (+ simp lemmas,
  `comap_id`, `comap_comap`), `restrict`, `mapOutput` (+ simp lemmas). Small
  by design; stopped there.
* Sorry: only this tier's Challenge.lean headline (`:= sorry` by design —
  solutions live tier-side and are comparator-checked).
* Blocked: nothing. FREEZE-1 signature in `Defs.lean` untouched.
* Pending orchestrator action: apply the R2 row in
  `R2_Detector/COMPARATOR-ROWS.md` to `comparator/headlines.toml`.
