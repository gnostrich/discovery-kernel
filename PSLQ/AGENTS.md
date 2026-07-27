# R1 agent — PSLQ (exact core, termination, empirical input)

Persistent charter + memory for the R1 tier agent. Read this fully at session
start; append to MEMORY after every significant step. Obey the root
`AGENTS.md` policies.

## Mission (strict order)

1. **DEPS.md verdict (blocker).** Locate and license-check the Hex library
   (Lean verified LLL/Gram–Schmidt, announced FLoC 2026, availability
   unverified). Write `PSLQ/DEPS.md`: HEX-USABLE (dependency + pin) or
   HEX-UNAVAILABLE (fall back to Mathlib primitives / self-contained rational
   Gram–Schmidt). No proofs before this verdict is committed.
2. **Exact-arithmetic core over ℚ.** We formalize the PSLQ-class detector in
   the CSV/HJLS normalization (Chen–Stehlé–Villard, ISSAC 2013: PSLQ ≡ HJLS
   up to scaling): textbook PSLQ's `H` matrix is irrational even on rational
   input; the HJLS normalization uses rational Gram–Schmidt data throughout,
   so every state is exactly representable over ℚ. Fuel-based iteration;
   state `(y, B, GSO data)` with invariant `y = x ⬝ B` (`B` unimodular).
   Prove partial correctness: report `m` ⟹ `IsIntRelation x m` (report site:
   a zero appears in `y`; the relation is the corresponding column of `B`;
   nonzero by unimodularity).
3. **Termination / lower bound** (Borwein–Lisoněk form): while no relation is
   reported, every integer relation of `x` has norm exceeding an explicit
   rational bound from the GSO data (`‖m‖² ≥ 1 / max_j ‖b*_j‖²`-shaped).
4. **THE TIER'S POINT — `pslq_empirical_sound`.** Already stated
   algorithm-independently in Challenge.lean; refine to mention the core's
   output once `pslq` lands (dated STATEMENTS.md note), keeping the
   algorithm-independent lemma as the engine.
5. **Last:** `instance : DiscoveryKernel` for the scalar lattice state
   against the FROZEN R2 signature (`R2_Detector/Defs.lean`).

Do NOT ship the core without the empirical theorem. No `Float` anywhere.

## Refinement duties

When `pslq` lands: refine `pslq_partial_correct`, `pslq_lower_bound`,
`pslq_empirical_sound` in Challenge.lean (R1 section, append-only edits of
the placeholder statements) with dated STATEMENTS.md changelog entries, and
fill your rows of `comparator/headlines.toml`.

## MEMORY (append-only, dated)

* 2026-07-27 — Tier initialized at FREEZE-0. Orchestrator note: no Aristotle
  MCP server exists in this session; use `scripts/aristotle.py` (API key in
  env). Hex verdict pending.
* 2026-07-27 — DEPS verdict written: **HEX-UNAVAILABLE** for this repo's pin.
  Hex is real (github.com/leanprover/hex, Apache-2.0, FLoC 2026) but pins
  Lean v4.32.0-rc1 + Mathlib v4.32.0-rc1-patch1 vs our v4.32.0 final — hard
  Lake graph conflict; also fit is partial (LLL/ℤ vs PSLQ-HJLS/ℚ). Fallback:
  self-contained rational linear algebra on plain Mathlib. Proofs unblocked.
* 2026-07-27 — EARLY WIN LANDED: `DiscoveryKernels.R1.pslq_empirical_sound`
  proven in PSLQ/Empirical.lean (statement copied verbatim from
  Challenge.lean; `lake build PSLQ` green; axioms = [propext,
  Classical.choice, Quot.sound] — exactly the default allowlist). No sorry.
* 2026-07-27 — STEERING CHANGE received: R2 dropped (no DiscoveryKernel
  instance), R0 moved out. Two new DEPS blockers completed: (a)
  certified-positivity studied → ADAPT verdict (checkPDq_sound Bool-check +
  soundness schema, margin transfer; no import, v4.28.0 pin); (b) prior-art
  negative recorded — no PSLQ formalization in any proof assistant (3 web
  searches, terms in DEPS.md). Interim status posted in TIER-STATUS.md.
  Resuming strict order: core + partial correctness next.
* 2026-07-27 — CORE LANDED. `PSLQ/Core.lean` compiles clean (9 errors
  fixed after the spend-limit kill: iota-reduce structure projections with
  `dsimp only` after `refine`; `Matrix.transvection_mul_transvection_same`
  takes `i j` EXPLICITLY before `h`; `List.find?_some` needs its result bound
  by `have` to avoid the `p := @decide _` higher-order misunification;
  `Fin`-valued `decreasing_by` needs `Fin.lt_def.mp`; `filterMap` binder
  needed an explicit `: Fin n` ascription or `(r : ℕ)` steals the binder
  type; `IsIntRelation` needed its own `Decidable` instance for the
  `checkPDq`-shaped Bool checker). PROVEN sorry-free:
  `pslq_partial_correct`, `ElemOp.apply_inv`, `PSLQState.report?_spec`,
  `checkRelation_sound`/`_iff`, `pslq_checkRelation`. Axioms = the default
  three on every one. `PSLQState.coords` was moved into `Core.lean` so
  `Challenge.lean` needs only `import PSLQ.Core`.
* 2026-07-27 — BOUND LANDED. `PSLQ/Bound.lean` (new): rational
  Gram–Schmidt orthogonality proved from scratch (Mathlib `gramSchmidt` needs
  `RCLike`, unusable over `ℚ`), `relation_eq_sum_smul_proj`
  (`m = ∑ z_j p_j` with `z = Binv·m`), `dotProduct_gso_eq`
  (`⟨m, b*_k⟩ = z_k‖b*_k‖²`), discrete Cauchy–Schwarz
  (`Finset.sum_mul_sq_le_sq_mul_sq`) and `z_k² ≥ 1` ⟹
  `pslq_lower_bound`. Sorry-free, default axioms. DESIGN NOTE for successors:
  the index `k` (top of the support of `Binv·m`) MUST appear in the
  statement — the `n` projected columns span the `(n-1)`-dim `x^⊥`, so
  exactly one GSO direction degenerates and any `min`-over-all-`j` packaging
  collapses to the trivial bound `0`. The `min` form survives only as the
  corollary `gsoNormSq_le_of_relation_of_min`.
* 2026-07-27 — `lakefile.toml` PSLQ glob `["PSLQ.+"]` RESTORED (the one
  authorized edit outside the tier dir); `lake build` green from the repo
  root, 8665 jobs. Deliverables written: `CHALLENGE-R1.proposed.md` (exact
  `pslq_lower_bound` replacement text, comparator-`isDefEq`-verified against
  the proof; `pslq_partial_correct` refinement had already been landed by the
  orchestrator with the identical statement) and `COMPARATOR-ROWS.md`. No
  Aristotle jobs were submitted this session — every obligation closed
  locally.
