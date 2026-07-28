# OV / R3 — proposed comparator rows (for the orchestrator to apply)

Tier agents do not edit `comparator/*`. Below are the exact replacements for
the six `[[headline]]` blocks with `tier = "R3"` in `comparator/headlines.toml`,
plus the corresponding `AxiomCheck.lean` pairs. Nothing else changes.

All five registered solutions were checked locally with the comparator's own
`isDefEq` test against the frozen `Challenge.lean` statements and with
`#print axioms`; results are recorded at the bottom.

## `comparator/headlines.toml` — replacement R3 rows

```toml
[[headline]]
name = "ov_license"
challenge = "DiscoveryKernels.Challenge.ov_license"
solution = ""
module = ""
proven_required = false
tier = "R3"

[[headline]]
name = "ov_completeness"
challenge = "DiscoveryKernels.Challenge.ov_completeness"
solution = ""
module = ""
proven_required = false
tier = "R3"

[[headline]]
name = "ov_condition_number_theorem"
challenge = "DiscoveryKernels.Challenge.ov_condition_number_theorem"
solution = "DiscoveryKernels.R3.ov_condition_number_theorem"
module = "OV.Proofs"
proven_required = false
tier = "R3"

[[headline]]
name = "ov_cnt_recovers_scalar"
challenge = "DiscoveryKernels.Challenge.ov_cnt_recovers_scalar"
solution = "DiscoveryKernels.R3.ov_cnt_recovers_scalar"
module = "OV.Proofs"
proven_required = false
tier = "R3"

[[headline]]
name = "ov_dist_not_element_valued"
challenge = "DiscoveryKernels.Challenge.ov_dist_not_element_valued"
solution = "DiscoveryKernels.R3.ov_dist_not_element_valued"
module = "OV.Proofs"
proven_required = false
tier = "R3"

[[headline]]
name = "ov_lojasiewicz_order"
challenge = "DiscoveryKernels.Challenge.ov_lojasiewicz_order"
solution = "DiscoveryKernels.R3.ov_lojasiewicz_order"
module = "OV.Proofs"
proven_required = false
tier = "R3"
```

Notes.

* `ov_license` stays unregistered: DECLARED-OPEN (MSY frontier), not attempted
  per steering.
* `ov_completeness` stays UNREGISTERED ON PURPOSE. `OV.Proofs` does contain
  `DiscoveryKernels.R3.ov_completeness` with a type definitionally equal to the
  challenge statement, but it carries ONE honest labelled `sorry`, so
  registering it would make the comparator fail its `sorryAx` check — correctly.
  Register it only once the gap below is closed. Two `sorry`-free conditional
  forms are available if the operator ever wants them registered against a
  *changed* statement:
  `DiscoveryKernels.R3.ov_completeness_of_star_scalars` and
  `DiscoveryKernels.R3.ov_completeness_of_starModule`.
* `proven_required` left at `false` for all six (the R3 mission flag); the
  operator may flip the four proven ones to `true` if the tier is now expected
  to keep them green.

## `comparator/AxiomCheck.lean` — nothing to do

`comparator.py::gen_lean` REGENERATES `AxiomCheck.lean` from
`headlines.toml` on every run (imports, `pairs`, and `#print axioms` lines all
derived from the rows). Applying the four rows above is therefore the whole
change; the `import OV.Proofs` and the four pairs/prints appear automatically.

## `comparator/allowlist.toml`

**No change requested.** No `native_decide`, no `Lean.ofReduceBool`, no
`Float`, no allowlist extension. All four registered solutions live inside the
default `["propext", "Classical.choice", "Quot.sound"]`.

## Local verification run (2026-07-28)

`isDefEq` against `Challenge.lean`, run with the comparator's own code path:

```
comparator: 5 statement match(es) OK
'DiscoveryKernels.R3.ov_dist_not_element_valued'   : [propext, Classical.choice, Quot.sound]
'DiscoveryKernels.R3.ov_condition_number_theorem'  : [propext, Classical.choice, Quot.sound]
'DiscoveryKernels.R3.ov_cnt_recovers_scalar'       : [propext, Classical.choice, Quot.sound]
'DiscoveryKernels.R3.ov_lojasiewicz_order'         : [propext, Classical.choice, Quot.sound]
'DiscoveryKernels.R3.ov_completeness_of_star_scalars' : [propext, Classical.choice, Quot.sound]
'DiscoveryKernels.R3.ov_completeness_of_starModule'   : [propext, Classical.choice, Quot.sound]
'DiscoveryKernels.R3.ov_completeness'              : [propext, sorryAx, Classical.choice, Quot.sound]
```

(The fifth match is `ov_completeness` — statement fidelity confirmed, proof
still carrying its labelled `sorry`; hence it is not registered above.)
