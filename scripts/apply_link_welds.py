#!/usr/bin/env python3
"""Generate and insert weld theorems from a saved `#zil_link` report.

Parses the report text produced by `#zil_link` / `#zil_link_module` (the exact
`renderHit` format), reconstructs each hit's substitution, conversion, and
prescription, reads both definitions' binder signatures from source, and emits
the weld theorem

    theorem <target>_eq_<cand>_scaled (<binders>) :
        <target> <args> = (<conversion·prescription>) * <cand> <σ⁻¹ args> := by
      unfold <target> <cand>
      ring

inserted into the target's concept-home before its `/- ZIL-END -/` marker (or
before the closing `end <Namespace>`), adding the candidate module's
`public import` when missing.  The build remains the arbiter: run the leaf
build after applying; a cycle or a wrong weld fails there, not silently.

Usage:
  python3 scripts/apply_link_welds.py --hits <report-file> --list
  python3 scripts/apply_link_welds.py --hits <report-file> \
      --select unruhTemperature:modularHamEigenvalue --dry-run
  python3 scripts/apply_link_welds.py --hits <report-file> --select ... --apply
"""

import argparse
import pathlib
import re
import subprocess
import sys

REPO = pathlib.Path(__file__).resolve().parent.parent

# ---------------------------------------------------------------- report parse

HIT_RE = re.compile(r"^\s+↦ (\S+)$")
META_RE = re.compile(r"^\s+σ: (.+?)\s{3}conversion: (.+?)\s{3}prescription: (.+)$")
TARGET_RE = re.compile(r"^zil link(?: module)?: (\S+)$")


def parse_report(text):
    hits = []
    target = None
    pending = None
    for line in text.splitlines():
        m = TARGET_RE.match(line)
        if m:
            target = m.group(1)
            continue
        # inside a module survey, per-decl headers look like "  <name>:"
        dm = re.match(r"^  (\S+):$", line)
        if dm:
            target = dm.group(1)
            continue
        m = HIT_RE.match(line)
        if m and target:
            pending = {"target": target, "cand": m.group(1)}
            continue
        m = META_RE.match(line)
        if m and pending:
            sigma = {}
            s = m.group(1).strip()
            if not s.startswith("(none"):
                for pair in s.split(", "):
                    a, _, b = pair.partition(" ↦ ")
                    sigma[a.strip()] = b.strip()
            pending["sigma"] = sigma
            pending["conversion"] = m.group(2).strip()
            pending["prescription"] = m.group(3).strip()
            hits.append(pending)
            pending = None
    return hits


# ------------------------------------------------------------- source lookup


def find_def(full_name):
    """Locate (file, binder-list) for a fully qualified definition name."""
    short = full_name.split(".")[-1]
    out = subprocess.run(
        ["grep", "-rln", "--include=*.lean",
         f"def {short} ", str(REPO / "Physlib")],
        capture_output=True, text=True).stdout.splitlines()
    for f in out:
        text = pathlib.Path(f).read_text()
        # namespace prefix must match the qualified name
        namespaces = re.findall(r"^namespace (\S+)$", text, re.M)
        if not any(full_name == f"{ns}.{short}" or
                   full_name.endswith(f"{ns}.{short}") for ns in namespaces):
            continue
        m = re.search(
            rf"^(?:noncomputable )?def {re.escape(short)}\s*((?:\([^)]*\)\s*)+):",
            text, re.M)
        if not m:
            continue
        binders = []
        for grp in re.findall(r"\(([^)]*)\)", m.group(1)):
            names, _, _ty = grp.partition(":")
            binders.extend(names.split())
        return pathlib.Path(f), binders
    return None, None


# ------------------------------------------------------------- lean rendering

SUP = str.maketrans("⁻¹²³⁴", "-1234")


def factor_to_lean(tok):
    """'kB^-1' → ('kB', -1); 'ℏ' → ('ℏ', 1); exponents may be fractions."""
    name, _, exp = tok.partition("^")
    if not exp:
        return name, 1
    try:
        num, _, den = exp.partition("/")
        e = float(num) / float(den) if den else float(num)
    except ValueError:
        e = None
    return name, e


def render_scale(conversion, prescription):
    """Render '(conversion · prescription)' as a Lean factor string, or None."""
    nums, dens = [], []
    if conversion != "1":
        for tok in conversion.split(" · "):
            name, e = factor_to_lean(tok)
            if e is None or e != int(e):
                return None  # fractional exponent: hand-treat
            e = int(e)
            (nums if e > 0 else dens).append(
                name if abs(e) == 1 else f"{name} ^ {abs(e)}")
    coeff = None
    if prescription != "exact":
        m = re.match(r"× (-?\d+(?:/\d+)?)(?: · π\^(-?\d+))?$", prescription)
        if not m:
            return None
        coeff = m.group(1)
        if m.group(2):
            pe = int(m.group(2))
            (nums if pe > 0 else dens).append(
                "Real.pi" if abs(pe) == 1 else f"Real.pi ^ {abs(pe)}")
    parts = []
    if coeff and coeff != "1":
        if "/" in coeff:
            a, b = coeff.split("/")
            parts.append(f"({a} / {b} : ℝ)")
        else:
            parts.append(f"({coeff} : ℝ)")
    parts.extend(nums)
    num = " * ".join(parts) if parts else "1"
    if dens:
        return f"{num} / ({' * '.join(dens)})"
    return num


def make_weld(hit):
    tfile, tbinders = find_def(hit["target"])
    cfile, cbinders = find_def(hit["cand"])
    if not tfile or not cfile:
        return None, f"signature not found for {hit['target']} / {hit['cand']}"
    inv = {v: k for k, v in hit["sigma"].items()}
    cargs = [inv.get(b, b) for b in cbinders]
    free = [a for a in cargs if a not in tbinders]
    # free candidate binders become extra universally quantified variables; if the
    # resulting statement is false (constants fail to cancel), `ring` fails at build.
    allbinders = tbinders + free
    scale = render_scale(hit["conversion"], hit["prescription"])
    if scale is None:
        return None, "fractional exponent or unparsed prescription; hand-treat"
    tshort = hit["target"].split(".")[-1]
    cshort = hit["cand"].split(".")[-1]
    name = f"{tshort}_eq_{cshort}_scaled"
    rhs = f"{hit['cand']} {' '.join(cargs)}"
    if scale != "1":
        rhs = f"({scale}) * {rhs}"
    stmt = (
        f"/-- Link found by `#zil_link`: `{tshort}` is `{cshort}` under "
        f"`{', '.join(f'{k} ↦ {v}' for k, v in hit['sigma'].items()) or 'the same names'}` "
        f"with conversion `{hit['conversion']}` and prescription "
        f"`{hit['prescription']}`. -/\n"
        f"theorem {name} ({' '.join(allbinders)} : ℝ) :\n"
        f"    {hit['target']} {' '.join(tbinders)}\n"
        f"      = {rhs} := by\n"
        f"  unfold {hit['target']} {hit['cand']}\n"
        f"  ring\n")
    return {"file": tfile, "text": stmt, "cand_file": cfile, "name": name}, None


def module_of(path):
    rel = path.resolve().relative_to(REPO)
    return str(rel.with_suffix("")).replace("/", ".")


def apply_weld(weld, dry):
    text = weld["file"].read_text()
    cand_mod = module_of(weld["cand_file"])
    changed = text
    if not re.search(rf"^public import {re.escape(cand_mod)}$", text, re.M):
        imports = list(re.finditer(r"^public import .*$", changed, re.M))
        pos = imports[-1].end()
        changed = changed[:pos] + f"\npublic import {cand_mod}" + changed[pos:]
    marker = "/- ZIL-END -/"
    block = "\n" + weld["text"]
    if marker in changed:
        idx = changed.index(marker)
        # insert before the ZIL block starts, i.e. before "/- ZIL-BEGIN -/" if present
        begin = changed.find("/- ZIL-BEGIN -/")
        at = begin if begin != -1 else idx
        changed = changed[:at] + weld["text"] + "\n" + changed[at:]
    else:
        m = list(re.finditer(r"^end \S+$", changed, re.M))
        at = m[-1].start() if m else len(changed)
        changed = changed[:at] + block + "\n" + changed[at:]
    if dry:
        print(f"--- would edit {weld['file']}\n{weld['text']}")
    else:
        weld["file"].write_text(changed)
        print(f"applied {weld['name']} → {weld['file']}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--hits", required=True)
    ap.add_argument("--list", action="store_true")
    ap.add_argument("--select", default="",
                    help="comma list of targetShort:candShort pairs")
    ap.add_argument("--dry-run", action="store_true")
    ap.add_argument("--apply", action="store_true")
    args = ap.parse_args()
    hits = parse_report(pathlib.Path(args.hits).read_text())
    if args.list:
        for h in hits:
            t = h["target"].split(".")[-1]
            c = h["cand"].split(".")[-1]
            print(f"{t}:{c}   σ={h['sigma']}  conv={h['conversion']}  "
                  f"presc={h['prescription']}")
        return
    wanted = {tuple(p.split(":")) for p in args.select.split(",") if p}
    for h in hits:
        key = (h["target"].split(".")[-1], h["cand"].split(".")[-1])
        if wanted and key not in wanted:
            continue
        weld, err = make_weld(h)
        if err:
            print(f"SKIP {key}: {err}", file=sys.stderr)
            continue
        apply_weld(weld, dry=not args.apply)


if __name__ == "__main__":
    main()
