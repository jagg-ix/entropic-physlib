#!/usr/bin/env python3
"""scripts/consolidate/consolidate.py — plan and apply module consolidation.

Three stages, each runnable on its own so a plan can be reviewed before anything is
written:

    plan    read stage-1 candidates, cluster them, emit a reviewable JSON plan
    apply   execute a plan: merge files, delete sources, repair imports repo-wide
    verify  build every host the plan touched, then the ZIL gate

Every safety rule below was learned by breaking something:

* **Namespaces are preserved verbatim.**  Each absorbed module keeps its own
  `namespace ... end`, so declaration full names never change and nothing outside the
  cluster can break.  Inferring a namespace from a file's `namespace` line and
  rewriting it repo-wide once corrupted 180 files, because one module declared the
  broad `Physlib.Thermodynamics`.
* **Sources are ordered topologically** by their import edges before concatenation.  A
  block placed before the lemma it consumes fails to elaborate.
* **Imports are repaired repo-wide**, manifest included, and duplicate import lines are
  collapsed only in files the merge already touched.
* **Rollback is file-level.**  A directory-level `git checkout` silently reverted an
  unrelated fix from an earlier merge in the same directory.
* **Nothing is written without `--apply`.**

Usage:
    consolidate.py plan   [--candidates FILE] [--max-files N] [--max-lines N] [--out FILE]
    consolidate.py apply  PLAN [--apply]
    consolidate.py verify PLAN
"""
from __future__ import annotations

import argparse
import json
import pathlib
import re
import subprocess
import sys
from collections import defaultdict

ROOT = pathlib.Path(__file__).resolve().parents[2]
MANIFEST = ROOT / "Physlib.lean"


# ---------------------------------------------------------------- helpers


def mod_to_path(mod: str) -> pathlib.Path:
    return ROOT / (mod.replace(".", "/") + ".lean")


def path_to_mod(path: pathlib.Path) -> str:
    return str(path.relative_to(ROOT))[: -len(".lean")].replace("/", ".")


def line_count(mod: str) -> int:
    p = mod_to_path(mod)
    return len(p.read_text().split("\n")) if p.exists() else 0


def imports_of(mod: str) -> list[str]:
    p = mod_to_path(mod)
    if not p.exists():
        return []
    return [l.split()[-1] for l in p.read_text().split("\n") if l.startswith("public import ")]


def declared_namespaces(mod: str) -> list[str]:
    p = mod_to_path(mod)
    if not p.exists():
        return []
    return [l.split()[1] for l in p.read_text().split("\n")
            if l.startswith("namespace ") and len(l.split()) > 1]


def all_module_names() -> list[str]:
    return [path_to_mod(p) for p in ROOT.glob("Physlib/**/*.lean")]


_SIZES: dict[str, int] = {}


def module_sizes() -> dict[str, int]:
    if not _SIZES:
        for p in ROOT.glob("Physlib/**/*.lean"):
            _SIZES[path_to_mod(p)] = len(p.read_text().split("\n"))
    return _SIZES


def repo_percentile(q: float) -> int:
    vals = sorted(module_sizes().values(), reverse=True)
    return vals[int(len(vals) * q)] if vals else 0


def size_budget(host: str, cluster: list[str], override: int) -> tuple[int, str]:
    """How large the merged module may be.

    A global constant is the wrong shape: this repository's directories keep genuinely
    different conventions (the FLRW modules sit near 250 lines, the entropic-time ones
    near 1400).  Nor is the directory maximum alone the right shape -- taken strictly it
    refuses a merge for overshooting by five lines.

    The budget is therefore the more generous of two measured quantities: the largest
    module the host's own directory already sustains, and the repository's 99th
    percentile.  A merge is allowed to produce something as large as its neighbourhood
    already tolerates, or as large as the repository's own upper tail, and is refused
    only when it would be an outlier by both measures.  `--max-lines` overrides it.
    """
    if override:
        return override, "explicit --max-lines"
    sizes = module_sizes()
    prefix = host.rsplit(".", 1)[0] + "."
    peers = [s for m, s in sizes.items() if m.startswith(prefix) and m not in cluster]
    tail = repo_percentile(0.01)           # p99 of module sizes
    local = max(peers) if peers else 0
    if local >= tail:
        return local, f"largest in {prefix.rstrip('.').split('.')[-1]}/"
    return tail, "repository p99"


# ---------------------------------------------------------------- plan


def read_candidates(path: pathlib.Path):
    pairs, frags, subjs = [], [], []
    for raw in path.read_text().split("\n"):
        parts = raw.rstrip().split("\t")
        if parts[0] == "PAIR" and len(parts) >= 5:
            pairs.append((parts[1], parts[2], int(parts[3]), int(parts[4])))
        elif parts[0] == "FRAG" and len(parts) >= 5:
            frags.append((parts[1], parts[2], int(parts[3]), int(parts[4])))
        elif parts[0] == "SUBJ" and len(parts) >= 3:
            subjs.append((parts[1], parts[2].split(",")))
    return pairs, frags, subjs


def cluster(edges: list[tuple[str, str]]) -> list[list[str]]:
    """Connected components over candidate edges."""
    parent: dict[str, str] = {}

    def find(x):
        parent.setdefault(x, x)
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(a, b):
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[ra] = rb

    for a, b in edges:
        union(a, b)
    groups = defaultdict(list)
    for m in parent:
        groups[find(m)].append(m)
    return [sorted(v) for v in groups.values() if len(v) > 1]


def toposort(mods: list[str]) -> list[str] | None:
    """Order so that a module comes after everything in the cluster it imports."""
    inside = set(mods)
    deps = {m: {d for d in imports_of(m) if d in inside and d != m} for m in mods}
    out, remaining = [], dict(deps)
    while remaining:
        ready = sorted([m for m, d in remaining.items() if not (d - set(out))])
        if not ready:
            return None  # cycle: Lean forbids it, so this means stale state
        out.extend(ready)
        for m in ready:
            remaining.pop(m)
    return out


def check_cluster(mods: list[str], max_lines: int) -> tuple[list[str] | None, list[str]]:
    """Return (ordered sources, blocking reasons)."""
    problems = []
    for m in mods:
        if not mod_to_path(m).exists():
            problems.append(f"missing file for {m}")
    if problems:
        return None, problems

    # a namespace that prefixes another module's path is a rewrite hazard; we do not
    # rewrite, but flag it so a reviewer knows declaration names are broad
    every = set(all_module_names())
    for m in mods:
        for ns in declared_namespaces(m):
            if ns in every and ns != m:
                problems.append(f"{m} declares broad namespace {ns} (kept verbatim)")

    order = toposort(mods)
    if order is None:
        problems.append("import cycle among cluster members")
        return None, problems

    total = sum(line_count(m) for m in mods)
    host_guess0 = max(mods, key=line_count)
    budget, why = size_budget(host_guess0, mods, max_lines)
    if total > budget:
        problems.append(f"merged size {total} exceeds the {budget}-line budget ({why})")
        return None, problems

    # The graph import reserves `this`, and that reservation propagates to everything
    # downstream: giving a host `meta import Zil` breaks anonymous-hypothesis proofs in
    # every module that imports it, not only in the cluster.
    # Merging unions the sources' public imports into the host, which can newly put the
    # graph language in scope for everything downstream. Its reserved `this` then breaks
    # every anonymous-hypothesis proof in that cone.
    host_guess = max(order, key=line_count)
    reserved = this_reserved_map()
    gains_zil = (not reserved.get(host_guess, False)) and any(
        reserved.get(d, False) or publicly_exports_zil(d)
        for m in mods for d in imports_of(m) if d not in mods)
    if gains_zil or (any(imports_zil(m) for m in mods) and not imports_zil(host_guess)):
        cone = downstream_cone(host_guess) | set(mods)
        offenders = sorted(m for m in cone if not reserved.get(m, False) and uses_bare_this(m))
        if offenders:
            problems.append("would put the graph language in scope, breaking anonymous "
                            "`this` in " + ", ".join(o.split(".")[-1] for o in offenders[:3])
                            + (f" (+{len(offenders) - 3} more)" if len(offenders) > 3 else ""))
            return None, problems
    return order, problems


def read_exclusions(path: pathlib.Path) -> set[frozenset[str]]:
    """Reviewed pairs to leave alone: `modA <space> modB  # reason`, one per line."""
    out = set()
    if not path.exists():
        return out
    for raw in path.read_text().split("\n"):
        line = raw.split("#")[0].strip()
        if not line:
            continue
        parts = line.split()
        if len(parts) >= 2:
            out.add(frozenset(parts[:2]))
    return out


def same_directory(a: str, b: str) -> bool:
    return a.rsplit(".", 1)[0] == b.rsplit(".", 1)[0]


def uses_bare_this(mod: str) -> bool:
    """Proofs that leave a hypothesis anonymous. The graph import reserves `this`, so a
    module using it cannot absorb (or be absorbed into) one that imports Zil."""
    p = mod_to_path(mod)
    if not p.exists():
        return False
    for l in p.read_text().split("\n"):
        s = l.strip()
        if s.startswith("have :") or s.startswith("have :=") or " this" in s or s.startswith("this"):
            if "have :" in s and "have : " not in s.replace("have :=", "have : "):
                return True
            if re.search(r"(^|[^A-Za-z_])this([^A-Za-z_]|$)", s):
                return True
    return False


def imports_zil(mod: str) -> bool:
    p = mod_to_path(mod)
    return p.exists() and "meta import Zil" in p.read_text()


def import_graph() -> dict[str, set[str]]:
    return {m: set(imports_of(m)) for m in all_module_names()}


def creates_cycle(cluster_mods: list[str], host: str) -> str | None:
    """Simulate the merge on the import graph and look for a cycle.

    Absorbing A into H gives H every import A had, and every module that imported A now
    imports H. If anything H depends on reaches H again, the merge is unbuildable.
    """
    g = import_graph()
    absorbed = set(cluster_mods) - {host}
    merged_imports = set()
    for m in cluster_mods:
        merged_imports |= g.get(m, set())
    merged_imports -= set(cluster_mods)
    new: dict[str, set[str]] = {}
    for m, deps in g.items():
        if m in absorbed:
            continue
        d = {host if x in absorbed else x for x in deps}
        d.discard(m)
        new[m] = d
    new[host] = {host if x in absorbed else x for x in merged_imports} - {host}
    # depth-first search from host
    seen, stack = set(), [host]
    while stack:
        cur = stack.pop()
        for nxt in new.get(cur, ()):  # noqa: B007
            if nxt == host:
                return f"merge would create an import cycle through {cur}"
            if nxt not in seen:
                seen.add(nxt)
                stack.append(nxt)
    return None


def publicly_exports_zil(mod: str) -> bool:
    """`public import Zil...` propagates the graph language's reserved tokens; plain
    `meta import Zil` does not."""
    p = mod_to_path(mod)
    if not p.exists():
        return False
    return any(re.match(r"public (meta )?import Zil\b", l)
               for l in p.read_text().split("\n"))


def this_reserved_map() -> dict[str, bool]:
    """A module has `this` reserved when its public-import closure reaches a module
    that publicly imports Zil."""
    mods = all_module_names()
    pub = {m: [d for d in imports_of(m)] for m in mods}
    roots = {m for m in mods if publicly_exports_zil(m)}
    memo: dict[str, bool] = {}

    def reach(m: str, seen: set[str]) -> bool:
        if m in memo:
            return memo[m]
        if m in roots:
            memo[m] = True
            return True
        if m in seen:
            return False
        seen.add(m)
        val = any(reach(d, seen) for d in pub.get(m, []))
        memo[m] = val
        return val

    return {m: reach(m, set()) for m in mods}


def downstream_cone(mod: str) -> set[str]:
    """Every module that transitively imports `mod`."""
    rev: dict[str, set[str]] = defaultdict(set)
    for m in all_module_names():
        for d in imports_of(m):
            rev[d].add(m)
    seen, stack = set(), [mod]
    while stack:
        cur = stack.pop()
        for up in rev.get(cur, ()):
            if up not in seen:
                seen.add(up)
                stack.append(up)
    return seen


def inbound_counts() -> dict[str, int]:
    """How many files mention each module's leaf name — a proxy for centrality."""
    counts: dict[str, int] = defaultdict(int)
    leaves = {m.rsplit(".", 1)[-1]: m for m in all_module_names()}
    for f in list(ROOT.glob("Physlib/**/*.lean")) + [MANIFEST]:
        text = f.read_text()
        for leaf, mod in leaves.items():
            if leaf in text:
                counts[mod] += 1
    return counts


def cmd_plan(args):
    pairs, frags, subjs = read_candidates(pathlib.Path(args.candidates))
    excluded = read_exclusions(pathlib.Path(args.exclusions))
    edges = [(a, b) for a, b, _, _ in pairs]
    if args.include_fragments:
        edges += [(a, b) for a, b, nd, _ in frags if nd <= args.fragment_max_decls]

    # "every citation goes to X" carries no information when X is cited by everyone:
    # a leaf that uses a hub is a consumer, not a fragment of it.
    inbound = inbound_counts()
    hubs = {m for m, n in inbound.items() if n >= args.hub_threshold}
    edges = [(a, b) for a, b in edges if not (b in hubs and a not in hubs)]

    dropped = []
    kept = []
    for a, b in edges:
        if frozenset((a, b)) in excluded:
            dropped.append((a, b, "reviewed exclusion"))
        elif not args.allow_cross_directory and not same_directory(a, b):
            dropped.append((a, b, "different directory: sector placement is meaningful"))
        else:
            kept.append((a, b))
    edges = kept

    clusters, skipped, used = [], [], 0
    for mods in sorted(cluster(edges), key=len, reverse=True):
        if used + len(mods) > args.max_files:
            skipped.append({"modules": mods, "reasons": ["round file budget reached"]})
            continue
        order, problems = check_cluster(mods, args.max_lines)
        blocking = [p for p in problems if "kept verbatim" not in p]
        if order is None or blocking:
            skipped.append({"modules": mods, "reasons": problems})
            continue
        host = max(order, key=line_count) if args.host_policy == "largest" else order[-1]
        cyc = creates_cycle(order, host)
        if cyc:
            skipped.append({"modules": mods, "reasons": [cyc]})
            continue
        clusters.append({
            "host": host,
            "host_path": str(mod_to_path(host).relative_to(ROOT)),
            "sources_in_order": order,
            "absorbed": [m for m in order if m != host],
            "merged_lines": sum(line_count(m) for m in order),
            "notes": problems,
        })
        used += len(mods)

    plan = {
        "clusters": clusters,
        "skipped": skipped,
        "not_considered": [{"a": a, "b": b, "reason": r} for a, b, r in dropped],
        "split_subjects_for_review": [{"subject": s, "modules": m} for s, m in subjs],
        "files_absorbed": sum(len(c["absorbed"]) for c in clusters),
        "modules_after": used - sum(1 for _ in clusters) if used else 0,
    }
    out = pathlib.Path(args.out)
    out.write_text(json.dumps(plan, indent=2) + "\n")
    print(f"plan written: {out}")
    print(f"  clusters: {len(clusters)}   files absorbed: {plan['files_absorbed']}"
          f"   skipped clusters: {len(skipped)}")
    for c in clusters:
        print(f"  · {c['host']}  ({c['merged_lines']} lines)")
        for m in c["absorbed"]:
            print(f"        ← {m}")
    for s in skipped:
        print(f"  ! skipped {', '.join(s['modules'])}: {'; '.join(s['reasons'])}")
    for a, b, r in dropped:
        print(f"  - not considered {a.split('.')[-1]} + {b.split('.')[-1]}: {r}")


# ---------------------------------------------------------------- apply


def split_file(mod: str):
    lines = mod_to_path(mod).read_text().split("\n")
    last_import = max(i for i, l in enumerate(lines)
                      if l.startswith(("public import ", "meta import ", "private import ", "import ")))
    imports = [l for l in lines if l.startswith("public import ")]
    metas = [l for l in lines if l.startswith("meta import ")]
    body = lines[last_import + 1:]
    while body and not body[0].strip():
        body.pop(0)
    while body and not body[-1].strip():
        body.pop()
    return imports, metas, body


def merge_cluster(c: dict) -> str:
    host, order = c["host"], c["sources_in_order"]
    absorbed = set(c["absorbed"])
    keep, seen, metas, blocks = [], set(), [], []
    for m in order:
        imp, met, body = split_file(m)
        for l in imp:
            target = l.split()[-1]
            if target in absorbed or target == host or l in seen:
                continue
            seen.add(l)
            keep.append(l)
        metas += met
        blocks.append((m, body))
    keep.sort(key=lambda l: (not l.split()[-1].startswith("Physlib"), l))
    out = ["/-", "Copyright (c) 2026 Jorge A. Garcia. All rights reserved.",
           "Released under Apache 2.0 license as described in the file LICENSE.",
           "Authors: Jorge A. Garcia", "-/", "module", ""] + keep + [""]
    if metas:
        out += sorted(set(metas)) + [""]
    for m, body in blocks:
        out += [f"/- Consolidated from {m} -/", ""] + body + [""]
    return "\n".join(out) + "\n"


HEADER_END = ("/-!", "namespace ", "@[expose]", "noncomputable ", "set_option ",
              "open ", "/-- ", "theorem ", "def ", "structure ")


def repair_imports(absorbed_to_host: dict[str, str]) -> list[str]:
    """Point imports of absorbed modules at their host.

    Import statements may wrap, with the module name on its own continuation line, so
    the header region is rewritten token-wise rather than by matching line starts.  The
    rewrite is confined to that region because a module name is also a namespace
    prefix: replacing it in the body would break references to declarations that the
    merge deliberately left where they were.
    """
    touched = []
    for f in list(ROOT.glob("Physlib/**/*.lean")) + [MANIFEST]:
        text = f.read_text()
        lines = text.split("\n")
        end = len(lines)
        for i, l in enumerate(lines):
            if l.startswith(HEADER_END):
                end = i
                break
        head, body, hit = lines[:end], lines[end:], False
        for i, l in enumerate(head):
            for gone, host in absorbed_to_host.items():
                if re.search(rf"(^|\s){re.escape(gone)}(\s|$)", l):
                    l = re.sub(rf"(^|\s){re.escape(gone)}(\s|$)", rf"\g<1>{host}\g<2>", l)
                    hit = True
            head[i] = l
        # collapse duplicate single-line imports the rewrite may have produced
        seen, deduped = set(), []
        for l in head:
            if l.startswith(("public import ", "import ")) and len(l.split()) > 2:
                if l in seen:
                    continue
                seen.add(l)
            deduped.append(l)
        new = "\n".join(deduped + body)
        if hit and new != text:
            f.write_text(new)
            touched.append(str(f.relative_to(ROOT)))
    return touched


def cmd_apply(args):
    plan = json.loads(pathlib.Path(args.plan).read_text())
    if not args.apply:
        print("DRY RUN — pass --apply to write. Planned actions:")
        for c in plan["clusters"]:
            print(f"  write {c['host_path']}  ({c['merged_lines']} lines)")
            for m in c["absorbed"]:
                print(f"    delete {mod_to_path(m).relative_to(ROOT)}")
        return

    absorbed_to_host, written = {}, []
    for c in plan["clusters"]:
        text = merge_cluster(c)
        mod_to_path(c["host"]).write_text(text)
        written.append(c["host"])
        for m in c["absorbed"]:
            mod_to_path(m).unlink()
            absorbed_to_host[m] = c["host"]
    touched = repair_imports(absorbed_to_host)
    # host must appear in the manifest exactly once
    man = MANIFEST.read_text()
    for host in written:
        if f"public import {host}\n" not in man:
            lines = man.split("\n")
            prefix = host.rsplit(".", 1)[0]
            siblings = [i for i, l in enumerate(lines)
                        if l.startswith(f"public import {prefix}.")]
            # Imports must precede everything else in a Lean file, so the fallback is
            # the end of the import block -- never the end of the file, which in this
            # manifest sits after a trailing docstring.
            all_imports = [i for i, l in enumerate(lines) if l.startswith("public import ")]
            idx = max(siblings) if siblings else max(all_imports)
            lines.insert(idx + 1, f"public import {host}")
            man = "\n".join(lines)
    MANIFEST.write_text(man)
    state = {"hosts": written, "absorbed": absorbed_to_host, "touched": touched}
    pathlib.Path(args.plan).with_suffix(".applied.json").write_text(json.dumps(state, indent=2) + "\n")
    print(f"applied: {len(written)} host(s), {len(absorbed_to_host)} file(s) absorbed,"
          f" {len(touched)} file(s) import-repaired")
    for h in written:
        print(f"  · {h}")


# ---------------------------------------------------------------- verify


def cmd_verify(args):
    plan = json.loads(pathlib.Path(args.plan).read_text())
    hosts = [c["host"] for c in plan["clusters"]]
    dangling = []
    for c in plan["clusters"]:
        for m in c["absorbed"]:
            for f in list(ROOT.glob("Physlib/**/*.lean")) + [MANIFEST]:
                if f"public import {m}\n" in f.read_text():
                    dangling.append((str(f.relative_to(ROOT)), m))
    if dangling:
        print("DANGLING IMPORTS (must be repaired before building):")
        for f, m in dangling:
            print(f"  {f} -> {m}")
        return 1
    print("no dangling imports")
    rc = subprocess.call(["lake", "build", *hosts], cwd=ROOT)
    if rc != 0:
        print("host build FAILED — roll back with file-level checkout:")
        print("  git checkout -- " + " ".join(sorted(
            {str(mod_to_path(h).relative_to(ROOT)) for h in hosts} |
            {"Physlib.lean"})))
        return rc
    print("hosts built; running the ZIL gate")
    return subprocess.call(["lake", "build", "Physlib.Meta.EntropicWepDepthGate"], cwd=ROOT)


# ---------------------------------------------------------------- cli


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)

    p = sub.add_parser("plan")
    p.add_argument("--candidates", default="scripts/consolidate/candidates.out")
    p.add_argument("--out", default="scripts/consolidate/plan.json")
    p.add_argument("--max-files", type=int, default=50,
                   help="file budget for one round (default 50)")
    p.add_argument("--max-lines", type=int, default=0,
                   help="hard line budget; 0 (default) derives it per directory from "
                        "the largest module that directory already sustains")
    p.add_argument("--host-policy", choices=["largest", "last"], default="largest")
    p.add_argument("--include-fragments", action="store_true",
                   help="also act on exclusive fragments, not only mutual pairs")
    p.add_argument("--fragment-max-decls", type=int, default=6)
    p.add_argument("--exclusions", default="scripts/consolidate/exclusions.txt")
    p.add_argument("--hub-threshold", type=int, default=20,
                   help="a module referenced by at least this many files is a hub; "
                        "fragment edges pointing at it are not evidence of a split")
    p.add_argument("--allow-cross-directory", action="store_true",
                   help="merge across directories; off by default because a module's "
                        "directory is its physics sector")
    p.set_defaults(func=cmd_plan)

    p = sub.add_parser("apply")
    p.add_argument("plan")
    p.add_argument("--apply", action="store_true", help="actually write (default dry run)")
    p.set_defaults(func=cmd_apply)

    p = sub.add_parser("verify")
    p.add_argument("plan")
    p.set_defaults(func=cmd_verify)

    args = ap.parse_args()
    sys.exit(args.func(args) or 0)


main()
