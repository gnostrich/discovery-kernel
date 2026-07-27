# AGENTS.md — orchestration charter (repo root)

This repository is developed by an orchestrator and persistent tier agents.
Each tier directory carries its own `AGENTS.md` (agent charter + persistent
MEMORY log) and `TIER-STATUS.md` (current state). Agents read their charter
and memory at session start and append to MEMORY after every significant
step, so work survives across sessions.

## Project constellation (revised scope, 2026-07-27)

| Repo | Role | Status |
|------|------|--------|
| `gnostrich/discovery-kernel` (this) | R1 (PSLQ) + R3 (OV statements) | active |
| `gnostrich/realization-lean` | scalar license: Kronecker realizability, rank stabilization, Kalman uniqueness, no-go, pole deletion, sym⊕skew decomposition, counterexample locks | active (Agent A) |
| `gnostrich/certified-positivity` | prior art: `checkPDq_sound` (decidable check proven sound), rational-enclosure / margin-transfer schemas, expand/halt certificates | **FROZEN — read/cite/import only, NEVER edit** |

R0 and R2 were descoped from this repo (see STATEMENTS.md changelog). No
abstract detector interface is designed up front; if ever wanted it gets
extracted from working instances (realization-lean's rank stabilization,
certified-positivity's expand/halt), not designed in advance.

## Tier ownership (hard rule)

| Agent | Owns | Challenge.lean section |
|-------|------|------------------------|
| R1    | `PSLQ/`      | `-- ==== R1 ====` |
| R3    | `OV/`        | `-- ==== R3 ====` |

An agent edits ONLY its own tier directory, its own Challenge.lean section
(append-only; statement changes require a dated STATEMENTS.md changelog
entry first), its own rows of STATEMENTS.md/comparator TOMLs, and its own
`AGENTS.md`/`TIER-STATUS.md`. Nothing else. Agent A owns the entire
`realization-lean` working copy (`/workspace/realization-lean`) and nothing
in this repo.

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
6. **R3 human-review gate.** R3 Challenge.lean entries merge only after
   operator approval, posted via TIER-STATUS.md.
7. **certified-positivity is frozen.** Read it, cite it, import from it —
   never edit it.

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
