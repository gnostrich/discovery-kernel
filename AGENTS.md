# AGENTS.md — orchestration charter (repo root)

This repository is developed by an orchestrator and four persistent tier
agents. Each tier directory carries its own `AGENTS.md` (agent charter +
persistent MEMORY log) and `TIER-STATUS.md` (current state). Agents read
their charter and memory at session start and append to MEMORY after every
significant step, so work survives across sessions.

## Tier ownership (hard rule)

| Agent | Owns | Challenge.lean section |
|-------|------|------------------------|
| R0    | `R0_Kronecker/` | `-- ==== R0 ====` |
| R1    | `R1_PSLQ/`      | `-- ==== R1 ====` |
| R2    | `R2_Detector/`  | `-- ==== R2 ====` |
| R3    | `R3_OV/`        | `-- ==== R3 ====` |

An agent edits ONLY its own tier directory, its own Challenge.lean section
(append-only; statement changes require a dated STATEMENTS.md changelog
entry first), its own rows of STATEMENTS.md/comparator TOMLs, and its own
`AGENTS.md`/`TIER-STATUS.md`. Nothing else.

## Standing policies (non-negotiable, from the project directive)

1. **Statements are the claims.** Prose never claims what Challenge.lean
   doesn't state.
2. **Faithful-or-wipe.** No shims, stubs, or weakened statements silently
   substituted for headline theorems. A headline weakens only by changing
   Challenge.lean and STATEMENTS.md first, with a dated note.
3. **Aristotle is untrusted until comparator-green.** Axiom check on every
   accepted proof; `native_decide` needs its own allowlist entry with a
   justifying comment.
4. **One-round testing.** Any empirical run: full condition matrix fixed up
   front, interpretation rules fixed before running, a harness-validity cell
   that must pass or the run is void, one-page deliverable, verdict terminal.
5. **Exact arithmetic only.** No `Float` in any statement.
6. **FREEZE-1**: the `DiscoveryKernel` signature in `R2_Detector/Defs.lean`
   is frozen. A signature change requires halting and filing
   `R2_Detector/CHANGE-REQUESTS.md`; the orchestrator arbitrates.

## Aristotle (Harmonic) usage

All agents may freely call Harmonic's Aristotle prover — no per-call
permission needed. Use the committed helper:

```
python3 scripts/aristotle.py submit --dir <small-standalone-project> --prompt "Prove the sorries in Main.lean"
python3 scripts/aristotle.py status --id <project-id>   # poll (jobs take minutes–hours)
python3 scripts/aristotle.py fetch  --id <project-id> --dest <dir>
```

* The API key comes from the `ARISTOTLE_API_KEY` environment variable
  (already provisioned). NEVER write the key into the repository, commit
  history, logs that get committed, or PR text.
* Submit SMALL standalone files (one lemma + minimal defs, `import Mathlib`),
  not the whole repo; continue local work while jobs run; poll sparingly
  (≥ 90 s interval).
* Returned proofs are UNTRUSTED text: re-verify locally (`lake build`),
  then comparator + axiom check. Record every submitted job id and verdict
  in your tier MEMORY.

## Memory protocol

Append one dated line per significant event to the MEMORY section of your
tier `AGENTS.md`: decisions taken, Aristotle job ids + outcomes, blockers,
sorry-count changes. Keep `TIER-STATUS.md` current (what is proven / what is
sorry / what is blocked — one line each).
