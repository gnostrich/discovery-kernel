# COMPARATOR-ROWS.md — R1 rows for `comparator/headlines.toml`

Prepared 2026-07-27 by the R1 agent. The orchestrator applies these.
All three R1 headlines now have a proved solution; every one is sorry-free
with axioms exactly `[propext, Classical.choice, Quot.sound]` (the default
allowlist — no `native_decide`, no extra axiom, no `Float`, no `ℝ` in the R1
core or bound).

## Rows (replace the existing R1 `[[headline]]` blocks verbatim)

```toml
[[headline]]
name = "pslq_partial_correct"
challenge = "DiscoveryKernels.Challenge.pslq_partial_correct"
solution = "DiscoveryKernels.R1.pslq_partial_correct"
module = "R1_PSLQ.Core"
proven_required = true
tier = "R1"

[[headline]]
name = "pslq_lower_bound"
challenge = "DiscoveryKernels.Challenge.pslq_lower_bound"
solution = "DiscoveryKernels.R1.pslq_lower_bound"
module = "R1_PSLQ.Bound"
proven_required = true
tier = "R1"

[[headline]]
name = "pslq_empirical_sound"
challenge = "DiscoveryKernels.Challenge.pslq_empirical_sound"
solution = "DiscoveryKernels.R1.pslq_empirical_sound"
module = "R1_PSLQ.Empirical"
proven_required = true
tier = "R1"
```

(The third row is unchanged from FREEZE-0 and is repeated only so the R1
block can be pasted as one piece.)

## `comparator/AxiomCheck.lean` additions

`AxiomCheck.lean` already imports `R1_PSLQ.Core` and carries the
`pslq_partial_correct` pair. For the lower bound it additionally needs

```lean
import R1_PSLQ.Bound
```

and the pair

```lean
    (`DiscoveryKernels.Challenge.pslq_lower_bound,
     `DiscoveryKernels.R1.pslq_lower_bound),
```

plus

```lean
#print axioms DiscoveryKernels.R1.pslq_lower_bound
```

## Verification performed locally (2026-07-27)

| check | result |
|-------|--------|
| `lake env lean R1_PSLQ/Core.lean` | exit 0, no errors, no warnings |
| `lake env lean R1_PSLQ/Bound.lean` | exit 0, no errors, no warnings |
| `lake build` (repo root, glob `R1_PSLQ.+` restored) | `Build completed successfully (8665 jobs)`; the only `sorry` warnings are the by-design `Challenge.lean` / `R3_OV` statement placeholders |
| `#print axioms` on `pslq_partial_correct`, `checkRelation_sound`, `PSLQState.report?_spec`, `ElemOp.apply_inv`, `pslq_checkRelation`, `gso_def` | `[propext, Classical.choice, Quot.sound]` |
| `#print axioms` on `pslq_lower_bound`, `PSLQState.gsoNormSq_le_of_relation`, `PSLQState.gsoNormSq_le_of_relation_of_min`, `gso_orthogonal`, `pslq_none_y_ne_zero`, `PSLQState.relation_eq_sum_smul_proj` | `[propext, Classical.choice, Quot.sound]` |
| comparator `isDefEq` mechanism run by hand on the proposed `pslq_lower_bound` Challenge text vs `R1.pslq_lower_bound` | `comparator: 1 statement match(es) OK` |
| `grep sorry` in `R1_PSLQ/Core.lean`, `R1_PSLQ/Bound.lean` | none (one prose occurrence in the `Bound.lean` module docstring) |
