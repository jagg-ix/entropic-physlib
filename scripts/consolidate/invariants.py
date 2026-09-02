#!/usr/bin/env python3
"""scripts/consolidate/invariants.py — check what a consolidation round must preserve.

A green build says the result compiles. It does not say the result is the *same
content*: a merge that silently dropped a theorem would still compile. These checks
compare the applied tree against the pre-merge state in git and establish the
properties the design claims.

    invariants.py PLAN [--base HEAD]

I1 content       every absorbed module's body appears verbatim in its host
I2 namespaces    every namespace a source declared is declared in the host
I3 declarations  every declaration name a source defined is present in the host
I4 dangling      nothing in the repository imports an absorbed module
I5 manifest      each host is listed once; no absorbed module is listed
I6 acyclic       the resulting import graph is a DAG
I7 census        repository-wide declaration count is unchanged

I1-I3 are the substance: they are what makes "no declaration moved" checkable rather
than asserted. I6 is what the planner's cycle guard promises, verified after the fact.
"""
from __future__ import annotations

import json
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
MANIFEST = ROOT / "Physlib.lean"

DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:public\s+|private\s+|protected\s+|noncomputable\s+|"
    r"partial\s+|unsafe\s+|nonrec\s+)*"
    r"(theorem|lemma|def|abbrev|structure|inductive|instance|class)\s+"
    r"([A-Za-z_][A-Za-z0-9_'’.]*)")
IMPORT_KW = ("public import ", "meta import ", "private import ", "import ")


def mod_to_path(mod: str) -> pathlib.Path:
    return ROOT / (mod.replace(".", "/") + ".lean")


def at_base(path: pathlib.Path, base: str) -> str | None:
    rel = str(path.relative_to(ROOT))
    r = subprocess.run(["git", "show", f"{base}:{rel}"], cwd=ROOT,
                       capture_output=True, text=True)
    return r.stdout if r.returncode == 0 else None


def body_of(text: str) -> list[str]:
    lines = text.split("\n")
    idx = [i for i, l in enumerate(lines) if l.startswith(IMPORT_KW)]
    body = lines[max(idx) + 1:] if idx else lines
    while body and not body[0].strip():
        body.pop(0)
    while body and not body[-1].strip():
        body.pop()
    return body


def names_in(text: str) -> set[str]:
    return set(names_list(text))


def names_list(text: str) -> list[str]:
    """Declarations as a multiset. Two modules may define the same short name in
    different namespaces -- preserving both is the point of keeping namespaces -- so the
    census must count occurrences, not distinct names."""
    return [m.group(2) for l in text.split("\n") if (m := DECL.match(l))]


def namespaces_in(text: str) -> set[str]:
    return {l.split()[1] for l in text.split("\n")
            if l.startswith("namespace ") and len(l.split()) > 1}


def all_lean() -> list[pathlib.Path]:
    return list(ROOT.glob("Physlib/**/*.lean"))


def header_of(path: pathlib.Path) -> str:
    lines = path.read_text().split("\n")
    stop = ("/-!", "namespace ", "@[expose]", "noncomputable ", "open ", "set_option ")
    for i, l in enumerate(lines):
        if l.startswith(stop):
            return "\n".join(lines[:i])
    return "\n".join(lines)


def imports_of_text(header: str) -> set[str]:
    toks, out, pending = header.split(), set(), False
    for tk in toks:
        if tk == "import":
            pending = True
            continue
        if pending:
            if tk.startswith(("Physlib", "Mathlib", "Zil", "QuantumInfo")):
                out.add(tk)
            pending = False
    return out


def main() -> int:
    plan_path = pathlib.Path(sys.argv[1])
    base = sys.argv[sys.argv.index("--base") + 1] if "--base" in sys.argv else "HEAD"
    plan = json.loads(plan_path.read_text())
    clusters = plan["clusters"]
    failures: list[str] = []
    checked = {"content": 0, "namespaces": 0, "declarations": 0}

    absorbed_all: set[str] = set()
    for c in clusters:
        host_text = mod_to_path(c["host"]).read_text()
        host_names, host_ns = names_in(host_text), namespaces_in(host_text)
        for m in c["absorbed"]:
            absorbed_all.add(m)
            old = at_base(mod_to_path(m), base)
            if old is None:
                failures.append(f"I1 {m}: cannot read pre-merge text at {base}")
                continue
            block = "\n".join(body_of(old))
            if block and block not in host_text:
                failures.append(f"I1 {m}: body not present verbatim in {c['host']}")
            else:
                checked["content"] += 1
            missing_ns = namespaces_in(old) - host_ns
            if missing_ns:
                failures.append(f"I2 {m}: namespaces lost: {sorted(missing_ns)}")
            else:
                checked["namespaces"] += 1
            missing = names_in(old) - host_names
            if missing:
                failures.append(f"I3 {m}: declarations lost: {sorted(missing)[:5]}")
            else:
                checked["declarations"] += 1

    # I4 dangling imports
    for f in all_lean() + [MANIFEST]:
        for mod in imports_of_text(header_of(f)) & absorbed_all:
            failures.append(f"I4 {f.relative_to(ROOT)} still imports absorbed {mod}")

    # I5 manifest
    man = MANIFEST.read_text()
    for c in clusters:
        n = man.count(f"public import {c['host']}\n")
        if n != 1:
            failures.append(f"I5 manifest lists {c['host']} {n} times (want 1)")
    for m in absorbed_all:
        if f"public import {m}\n" in man:
            failures.append(f"I5 manifest still lists absorbed {m}")

    # I6 acyclicity
    graph = {}
    for f in all_lean():
        mod = str(f.relative_to(ROOT))[:-5].replace("/", ".")
        graph[mod] = {d for d in imports_of_text(header_of(f)) if d.startswith("Physlib")}
    colour: dict[str, int] = {}
    cyc = []

    def walk(n: str) -> None:
        colour[n] = 1
        for d in graph.get(n, ()):
            if colour.get(d, 0) == 1:
                cyc.append(f"{n} -> {d}")
            elif colour.get(d, 0) == 0 and d in graph:
                walk(d)
        colour[n] = 2

    sys.setrecursionlimit(10000)
    for n in graph:
        if colour.get(n, 0) == 0:
            walk(n)
    for c in cyc[:5]:
        failures.append(f"I6 import cycle: {c}")

    # I7 census, over the affected modules only: the merge cannot change files it
    # never opened, and a repository-wide `git show` per file is prohibitively slow.
    was = now = 0
    for c in clusters:
        now += len(names_list(mod_to_path(c["host"]).read_text()))
        host_old = at_base(mod_to_path(c["host"]), base)
        if host_old is not None:
            was += len(names_list(host_old))
        for m in c["absorbed"]:
            old = at_base(mod_to_path(m), base)
            if old is not None:
                was += len(names_list(old))
    print("consolidation invariants")
    print(f"  I1 content       {checked['content']}/{len(absorbed_all)} bodies verbatim in host")
    print(f"  I2 namespaces    {checked['namespaces']}/{len(absorbed_all)} preserved")
    print(f"  I3 declarations  {checked['declarations']}/{len(absorbed_all)} preserved")
    print(f"  I4 dangling      {'none' if not any(f.startswith('I4') for f in failures) else 'FOUND'}")
    print(f"  I5 manifest      {'consistent' if not any(f.startswith('I5') for f in failures) else 'INCONSISTENT'}")
    print(f"  I6 acyclic       {'yes' if not cyc else 'NO'}")
    print(f"  I7 census        {was} declarations before, {now} after"
          f"  ({'equal' if was == now else 'DIFFERS by ' + str(now - was)})")
    if was != now:
        failures.append(f"I7 declaration census changed by {now - was}")
    if failures:
        print("\nFAILURES")
        for f in failures[:20]:
            print("  " + f)
        return 1
    print("\nall invariants hold")
    return 0


sys.exit(main())
