#!/usr/bin/env python3
"""Machine-check this repository's prior-art claims about the pinned Mathlib.

The comparator verifies *statements* and *axioms*. Nothing verified the
*sweeps* — and on 2026-07-28 a sweep claim ("Mathlib has no Gershgorin") was
found to be false. This script closes that hole: every absence/presence claim
registered in `comparator/absence-claims.toml` is re-checked against the
pinned Mathlib checkout, and a false claim fails the build.

Exit code 0 iff every registered claim holds.
"""

import pathlib
import subprocess
import sys
import tomllib

ROOT = pathlib.Path(__file__).resolve().parent.parent
MATHLIB = ROOT / ".lake" / "packages" / "mathlib" / "Mathlib"


def hits(term: str) -> list[str]:
    """Files in the pinned Mathlib containing `term` (case-insensitive)."""
    proc = subprocess.run(
        ["grep", "-ril", "--include=*.lean", term, str(MATHLIB)],
        capture_output=True, text=True)
    # grep exits 1 on "no matches", which is not an error for us.
    if proc.returncode not in (0, 1):
        sys.exit(f"sweep_check: grep failed for {term!r}: {proc.stderr.strip()}")
    return [l for l in proc.stdout.splitlines() if l.strip()]


def main() -> None:
    if not MATHLIB.is_dir():
        sys.exit(f"sweep_check: pinned Mathlib not found at {MATHLIB} "
                 "(run `lake exe cache get` first)")

    with open(ROOT / "comparator" / "absence-claims.toml", "rb") as f:
        cfg = tomllib.load(f)

    failures = []

    for entry in cfg.get("absent", []):
        found = hits(entry["term"])
        if found:
            rel = [str(pathlib.Path(p).relative_to(MATHLIB.parent)) for p in found[:5]]
            failures.append(
                f"FALSE ABSENCE CLAIM: {entry['term']!r} IS present in the pinned "
                f"Mathlib ({len(found)} file(s), e.g. {rel}).\n"
                f"    claim on record: {entry['claim']}")
        else:
            print(f"sweep_check: absent OK  — {entry['term']!r}")

    for entry in cfg.get("present", []):
        found = hits(entry["term"])
        if not found:
            failures.append(
                f"FALSE PRESENCE CLAIM: {entry['term']!r} is NOT in the pinned "
                f"Mathlib.\n    claim on record: {entry['claim']}")
        else:
            print(f"sweep_check: present OK — {entry['term']!r} ({len(found)} file(s))")

    if failures:
        print("\nsweep_check: FAIL\n")
        for f in failures:
            print("  " + f)
        print("\nA prior-art claim in this repository's prose is wrong. Fix the "
              "prose and the claim registry before merging.")
        sys.exit(1)

    print(f"sweep_check: PASS ({len(cfg.get('absent', []))} absence + "
          f"{len(cfg.get('present', []))} presence claims verified)")


if __name__ == "__main__":
    main()
