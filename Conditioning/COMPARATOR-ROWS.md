# COMPARATOR-ROWS.md — Conditioning rows for `comparator/headlines.toml`

Prepared 2026-07-27 by the Conditioning tier agent. The orchestrator applies
these; the agent does not edit `comparator/*`.

All six Conditioning headlines have a proved solution. Every one is
**sorry-free** with axioms exactly `[propext, Classical.choice, Quot.sound]` —
the default allowlist. **No allowlist extension is requested**: there is no
`native_decide`, no `Lean.ofReduceBool`, no extra axiom, and no `Float`
anywhere in `Conditioning/`.

## Rows (append as one block to `comparator/headlines.toml`)

```toml
[[headline]]
name = "cond_check_sound"
challenge = "DiscoveryKernels.Challenge.cond_check_sound"
solution = "DiscoveryKernels.Cond.condCheck_sound"
module = "Conditioning.Checker"
proven_required = true
tier = "COND"

[[headline]]
name = "cond_dist_to_illposed"
challenge = "DiscoveryKernels.Challenge.cond_dist_to_illposed"
solution = "DiscoveryKernels.Cond.condCheck_le_infDist"
module = "Conditioning.Bridge"
proven_required = true
tier = "COND"

[[headline]]
name = "cond_licenses_computation"
challenge = "DiscoveryKernels.Challenge.cond_licenses_computation"
solution = "DiscoveryKernels.Cond.condCheck_licenses_solve"
module = "Conditioning.Checker"
proven_required = true
tier = "COND"

[[headline]]
name = "cond_eigenvalue_margin"
challenge = "DiscoveryKernels.Challenge.cond_eigenvalue_margin"
solution = "DiscoveryKernels.Cond.condCheck_hermitian_eigenvalue_margin"
module = "Conditioning.Bridge"
proven_required = true
tier = "COND"

[[headline]]
name = "cond_margin_sharp"
challenge = "DiscoveryKernels.Challenge.cond_margin_sharp"
solution = "DiscoveryKernels.Cond.diag_dist_exact"
module = "Conditioning.Sharpness"
proven_required = true
tier = "COND"

[[headline]]
name = "cond_gershgorin_wall"
challenge = "DiscoveryKernels.Challenge.cond_gershgorin_wall"
solution = "DiscoveryKernels.Cond.gershgorin_wall"
module = "Conditioning.Sharpness"
proven_required = true
tier = "COND"
```

## `comparator/allowlist.toml`

**No change required.** The `default = ["propext", "Classical.choice",
"Quot.sound"]` entry covers every Conditioning solution. Verified by
`#print axioms` on all six solutions plus every supporting lemma (table below).

## `comparator/AxiomCheck.lean` additions

Add the imports

```lean
import Conditioning.Sharpness
import Conditioning.Bridge
```

the pairs

```lean
    (`DiscoveryKernels.Challenge.cond_check_sound,
     `DiscoveryKernels.Cond.condCheck_sound),
    (`DiscoveryKernels.Challenge.cond_dist_to_illposed,
     `DiscoveryKernels.Cond.condCheck_le_infDist),
    (`DiscoveryKernels.Challenge.cond_licenses_computation,
     `DiscoveryKernels.Cond.condCheck_licenses_solve),
    (`DiscoveryKernels.Challenge.cond_eigenvalue_margin,
     `DiscoveryKernels.Cond.condCheck_hermitian_eigenvalue_margin),
    (`DiscoveryKernels.Challenge.cond_margin_sharp,
     `DiscoveryKernels.Cond.diag_dist_exact),
    (`DiscoveryKernels.Challenge.cond_gershgorin_wall,
     `DiscoveryKernels.Cond.gershgorin_wall),
```

and the prints

```lean
#print axioms DiscoveryKernels.Cond.condCheck_sound
#print axioms DiscoveryKernels.Cond.condCheck_le_infDist
#print axioms DiscoveryKernels.Cond.condCheck_licenses_solve
#print axioms DiscoveryKernels.Cond.condCheck_hermitian_eigenvalue_margin
#print axioms DiscoveryKernels.Cond.diag_dist_exact
#print axioms DiscoveryKernels.Cond.gershgorin_wall
```

## `lakefile.toml` — REQUIRED ORCHESTRATOR ACTION

There is **no `Conditioning` library** in `lakefile.toml` yet, so `lake build`
does not see this tier. Please add

```toml
[[lean_lib]]
name = "Conditioning"
globs = ["Conditioning.+"]
```

and add `"Conditioning"` to `defaultTargets`.

**Caveat:** the glob `Conditioning.+` will also try to elaborate
`Conditioning/CHALLENGE-COND.proposed.lean`. That file is a *proposal* and
contains six by-design `sorry`s; it also is not a legal Lean module name
(dashes/dots). Either (a) list the modules explicitly instead of globbing:

```toml
[[lean_lib]]
name = "Conditioning"
roots = ["Conditioning.Sharpness", "Conditioning.Bridge"]
```

or (b) move `CHALLENGE-COND.proposed.lean` out of the library path once its
content has been merged into `Challenge.lean`. Option (b) is cleaner; the
proposal file exists only until the merge.

Until the library exists, every module in this tier verifies with

```
lake env lean Conditioning/<Module>.lean
```

after its dependencies' `.olean`s are placed under
`.lake/build/lib/lean/Conditioning/` (the agent did this by hand with
`lake env lean <file> -o .lake/build/lib/lean/Conditioning/<Mod>.olean`).

## Verification performed locally (2026-07-27)

| check | result |
|-------|--------|
| `lake env lean Conditioning/Defs.lean` | exit 0, no errors, no warnings |
| `lake env lean Conditioning/Gershgorin.lean` | exit 0, no errors, no warnings |
| `lake env lean Conditioning/Margin.lean` | exit 0, no errors (1 `unusedVariables` lint) |
| `lake env lean Conditioning/Checker.lean` | exit 0, no errors, no warnings |
| `lake env lean Conditioning/Sharpness.lean` | exit 0, no errors (4 style lints) |
| `lake env lean Conditioning/Bridge.lean` | exit 0, no errors (3 style/deprecation lints) |
| `lake env lean Conditioning/CHALLENGE-COND.proposed.lean` | exit 0; exactly 6 `declaration uses sorry` warnings, all by design |
| comparator `isDefEq` mechanism, hand-run on all 6 challenge/solution pairs | all 6 elaborate: each proposed Challenge type, transcribed verbatim, is inhabited by its solution constant |
| `#print axioms` on all 6 solutions | `[propext, Classical.choice, Quot.sound]` |
| `#print axioms` on 20 supporting lemmas (`gershgorin_rayleigh_floor`, `gershgorin_disc`, `quadForm_gram`, `sigmaMinGE_of_gram_floor`, `det_ne_zero_of_sigmaMinGE`, `abs_eigenvalue_ge_of_sigmaMinGE`, `distGE_of_sigmaMinGE`, `distGE_zero_vacuous`, `specNormLe_inv_of_sigmaMinGE`, `solve_error_bound`, `condCheck_distGE`, `condCheck_abs_eigenvalue`, `discCheck_abs_eigenvalue`, `det_ne_zero_of_strict_diag_dominance`, `specNormLe_of_l2_opNorm_le`, `sigmaMinGE_iff_norm`, `le_infDist_sigmaSing_of_distGE`, `isEigenvalue_eigenvalues`, `singular_dist_zero`, `diagA_condCheck`) | `[propext, Classical.choice, Quot.sound]` on every one |
| `grep -n sorry Conditioning/*.lean` | no `sorry` in any tier module (one prose occurrence in a `Sharpness.lean` docstring); the only `sorry`s are the six in the *proposal* file, by design |
| `grep -n Float Conditioning/*.lean` | no `Float`; only prose occurrences saying there is none |
| `grep -n native_decide Conditioning/*.lean` | no `native_decide`; only prose occurrences saying there is none |
