#!/usr/bin/env python3
"""Comparator: statement-fidelity and axiom audit for discovery-kernels.

Checks, per headline registered in comparator/headlines.toml:

1. Challenge.lean still declares the headline and its proof is literally
   `sorry` (the challenge file is a statement registry, never a proof site).
2. If a solution constant is registered: the solution's TYPE is definitionally
   equal to the challenge statement (checked inside Lean; this subsumes
   "syntactically identical up to whitespace" and is robust to formatting).
3. `#print axioms` of the solution is within allowlist.toml
   (default + per-theorem `extra`); `sorryAx` is always fatal for solutions.
4. With --strict: every `proven_required` headline must have a solution.

Exit code 0 iff all checks pass.
"""

import argparse
import pathlib
import re
import subprocess
import sys
import tomllib

ROOT = pathlib.Path(__file__).resolve().parent.parent
GEN = ROOT / "comparator" / "AxiomCheck.lean"


def fail(msg: str) -> None:
    print(f"comparator: FAIL: {msg}")
    sys.exit(1)


def load():
    with open(ROOT / "comparator" / "headlines.toml", "rb") as f:
        heads = tomllib.load(f)["headline"]
    with open(ROOT / "comparator" / "allowlist.toml", "rb") as f:
        allow = tomllib.load(f)
    return heads, allow


def check_challenge_file(heads):
    src = (ROOT / "Challenge.lean").read_text()
    for h in heads:
        name = h["name"]
        # Find the declaration and require its body to be literally `sorry`.
        decls = re.findall(
            rf"^theorem {re.escape(name)}\b(.*?):=\s*(\S+)\s*$",
            src, re.M | re.S)
        if len(decls) != 1:
            fail(f"Challenge.lean must declare `theorem {name}` exactly once "
                 f"(found {len(decls)})")
        if decls[0][1] != "sorry":
            fail(f"Challenge.lean: `{name}` must be `:= sorry` (statement "
                 f"registry, never a proof site); found `{decls[0][1]}`")
    print(f"comparator: Challenge.lean registry check OK "
          f"({len(heads)} headlines, all `sorry`)")


def gen_lean(heads) -> list:
    """Generate AxiomCheck.lean; return the solution constants audited."""
    imports = {"Challenge"}
    for h in heads:
        if h["module"]:
            imports.add(h["module"])
    lines = [f"import {m}" for m in sorted(imports)]
    lines += ["open Lean Elab Command Meta in", "run_cmd liftTermElabM do"]
    pairs = [(h["challenge"], h["solution"]) for h in heads if h["solution"]]
    if pairs:
        lines.append("  let pairs : List (Name × Name) := [")
        lines.append(
            ",\n".join(f"    (`{c}, `{s})" for c, s in pairs))
        lines.append("  ]")
        lines += [
            "  for (c, s) in pairs do",
            "    let ci ← getConstInfo c",
            "    let si ← getConstInfo s",
            "    unless ci.levelParams.length == si.levelParams.length do",
            "      throwError \"universe parameter mismatch: {c} vs {s}\"",
            "    let ls := ci.levelParams.map Level.param",
            "    let ct := ci.instantiateTypeLevelParams ls",
            "    let st := si.instantiateTypeLevelParams ls",
            "    unless (← isDefEq ct st) do",
            "      throwError \"statement mismatch: {c} vs {s}\"",
            "  logInfo s!\"comparator: {pairs.length} statement match(es) OK\"",
        ]
    else:
        lines.append("  logInfo \"comparator: no solutions registered yet\"")
    for h in heads:
        if h["solution"]:
            lines.append(f"#print axioms {h['solution']}")
    GEN.write_text("\n".join(lines) + "\n")
    return [h["solution"] for h in heads if h["solution"]]


def parse_axioms(output: str) -> dict:
    """Parse `#print axioms` output into {const: [axioms]}."""
    res = {}
    for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output):
        res[m.group(1)] = [a.strip() for a in m.group(2).split(",") if a.strip()]
    for m in re.finditer(r"'([^']+)' does not depend on any axioms", output):
        res[m.group(1)] = []
    return res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--strict", action="store_true",
                    help="require a solution for every proven_required headline")
    args = ap.parse_args()

    heads, allow = load()
    check_challenge_file(heads)

    if args.strict:
        missing = [h["name"] for h in heads
                   if h["proven_required"] and not h["solution"]]
        if missing:
            fail(f"--strict: proven_required headlines without solutions: {missing}")

    sols = gen_lean(heads)
    proc = subprocess.run(
        ["lake", "env", "lean", str(GEN)],
        cwd=ROOT, capture_output=True, text=True)
    out = proc.stdout + proc.stderr
    if proc.returncode != 0:
        print(out)
        fail("AxiomCheck.lean failed (statement mismatch or build error above)")

    axioms = parse_axioms(out)
    default = set(allow["default"])
    for h in heads:
        s = h["solution"]
        if not s:
            if h["proven_required"]:
                print(f"comparator: WARN: no solution yet for {h['name']}")
            continue
        if s not in axioms:
            fail(f"no `#print axioms` output for {s}")
        used = set(axioms[s])
        if "sorryAx" in used:
            fail(f"{s} depends on sorryAx")
        allowed = default | set(allow.get(s, {}).get("extra", []))
        bad = used - allowed
        if bad:
            fail(f"{s} uses axioms outside allowlist: {sorted(bad)}")
        print(f"comparator: {h['name']}: axioms OK {sorted(used)}")
    print(f"comparator: PASS ({len(sols)} solution(s) audited)")


if __name__ == "__main__":
    main()
