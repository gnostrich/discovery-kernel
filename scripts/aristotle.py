#!/usr/bin/env python3
"""CLI wrapper around Harmonic's Aristotle prover (aristotlelib >= 2.x).

Reads the API key from the ARISTOTLE_API_KEY environment variable. The key is
NEVER stored in this repository.

Policy (see AGENTS.md): Aristotle output is UNTRUSTED until it (a) compiles in
this repo, (b) passes the comparator statement check, and (c) passes the
per-theorem axiom allowlist check.

Usage:
  aristotle.py submit --dir DIR --prompt "..."     # submit a Lean project dir
  aristotle.py status --id PROJECT_ID              # one-shot status + tasks
  aristotle.py wait --id PROJECT_ID [--timeout S]  # poll until IDLE
  aristotle.py fetch --id PROJECT_ID --dest DIR    # download result archive
  aristotle.py ask --id PROJECT_ID --prompt "..."  # follow-up instruction
  aristotle.py list                                # recent projects

Typical agent flow: write a SMALL standalone .lean file (statement + minimal
defs, `import Mathlib`) into a fresh dir, `submit` it with a prompt like
"Prove the sorries in Main.lean", continue local work, `wait`/`status` later,
`fetch` and inspect the returned file, then re-verify locally.

Note: every `aristotlelib.Project` method is a coroutine, so each command
below is async and driven by `asyncio.run`.
"""

import argparse
import asyncio
import os
import sys


def _project_cls():
    if not os.environ.get("ARISTOTLE_API_KEY"):
        sys.exit("ARISTOTLE_API_KEY not set")
    import aristotlelib  # noqa: F401  (key picked up from env)
    from aristotlelib.project import Project
    return Project


async def cmd_submit(args):
    Project = _project_cls()
    p = await Project.create_from_directory(prompt=args.prompt, project_dir=args.dir)
    print(p.object_id)


async def _print_status(p):
    print(f"project {p.object_id}: status={p.status.name} updated={p.last_updated}")
    try:
        tasks, _ = await p.get_tasks(limit=5)
        for t in tasks:
            desc = (getattr(t, "description", "") or "").replace("\n", " ")[:120]
            print(f"  task {getattr(t, 'status', '?')}: {desc}")
    except Exception as e:  # noqa: BLE001 - status is best-effort
        print(f"  (tasks unavailable: {e})")


async def cmd_status(args):
    Project = _project_cls()
    await _print_status(await Project.from_id(args.id))


async def cmd_wait(args):
    Project = _project_cls()
    loop = asyncio.get_running_loop()
    deadline = loop.time() + args.timeout
    while True:
        p = await Project.from_id(args.id)
        await _print_status(p)
        if p.status.name == "IDLE":
            return
        if loop.time() > deadline:
            sys.exit(f"timeout after {args.timeout}s (still {p.status.name})")
        await asyncio.sleep(args.poll)


async def cmd_fetch(args):
    Project = _project_cls()
    p = await Project.from_id(args.id)
    print(await p.get_files(destination=args.dest))


async def cmd_ask(args):
    Project = _project_cls()
    p = await Project.from_id(args.id)
    await p.ask(args.prompt)
    print("sent")


async def cmd_list(args):
    Project = _project_cls()
    projects, _ = await Project.list_projects(limit=args.limit)
    for p in projects:
        desc = (p.description or "").replace("\n", " ")[:80]
        print(f"{p.object_id}  {p.status.name:8s}  {p.created_at}  {desc}")


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)

    s = sub.add_parser("submit"); s.add_argument("--dir", required=True)
    s.add_argument("--prompt", required=True); s.set_defaults(fn=cmd_submit)

    s = sub.add_parser("status"); s.add_argument("--id", required=True)
    s.set_defaults(fn=cmd_status)

    s = sub.add_parser("wait"); s.add_argument("--id", required=True)
    s.add_argument("--timeout", type=int, default=3600)
    s.add_argument("--poll", type=int, default=90); s.set_defaults(fn=cmd_wait)

    s = sub.add_parser("fetch"); s.add_argument("--id", required=True)
    s.add_argument("--dest", required=True); s.set_defaults(fn=cmd_fetch)

    s = sub.add_parser("ask"); s.add_argument("--id", required=True)
    s.add_argument("--prompt", required=True); s.set_defaults(fn=cmd_ask)

    s = sub.add_parser("list"); s.add_argument("--limit", type=int, default=15)
    s.set_defaults(fn=cmd_list)

    args = ap.parse_args()
    asyncio.run(args.fn(args))


if __name__ == "__main__":
    main()
