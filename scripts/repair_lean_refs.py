#!/usr/bin/env python3
"""Repair rotten lean: tokens in ZIL attach blocks.

Input: a TSV from `#zil_lean_refs_report` (lines: ROTTEN\t<carrier>\t<lean:token>).
For each unresolved reference, find the declaration's current home by searching
Physlib (then Mathlib) sources for its final name component, reconstruct the full
name from the enclosing namespaces, and rewrite every occurrence of the old token.

Classes:
  FIX        unique candidate found, token rewritten (with --apply)
  VISIBILITY a source declaration already has exactly the referenced name
             (the gate's module context cannot see it — repair is exposure, not renaming)
  AMBIGUOUS  several candidates — manual triage
  MISSING    no candidate — deleted or drifted beyond name match, manual triage
"""
import re
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
MATHLIB = REPO / ".lake" / "packages" / "mathlib" / "Mathlib"
DECL_RE = None  # built per short name

DECL_KINDS = r"(?:theorem|lemma|def|abbrev|structure|class|instance|inductive|opaque)"
MODIFIERS = r"(?:public\s+|private\s+|protected\s+|noncomputable\s+|meta\s+|@\[[^\]]*\]\s*)*"


def find_candidates(short: str, roots):
    """All (file, computed-full-name) whose declaration name ends in `short`."""
    pat = rf"^\s*{MODIFIERS}{DECL_KINDS}\s+((?:[\w'ᵥₙ₀-₉ₐ-ₜα-ωΑ-Ω℘ℏ]+\.)*{re.escape(short)})\b"
    rx = re.compile(pat)
    out = []
    for root in roots:
        try:
            hits = subprocess.run(
                ["grep", "-rlE", f"{DECL_KINDS} +([A-Za-z_0-9'.]*\\.)?{short}", str(root),
                 "--include=*.lean"],
                capture_output=True, text=True, timeout=120).stdout.split()
        except subprocess.TimeoutExpired:
            continue
        for f in hits:
            path = Path(f)
            stack = []
            for line in path.read_text(encoding="utf-8").splitlines():
                mns = re.match(r"^namespace\s+([\w'.₀-₉ₐ-ₜ]+)\s*$", line)
                mend = re.match(r"^end\s+([\w'.₀-₉ₐ-ₜ]+)\s*$", line)
                if mns:
                    stack.append(mns.group(1))
                elif mend and stack and stack[-1] == mend.group(1):
                    stack.pop()
                else:
                    md = rx.match(line)
                    if md:
                        full = ".".join(stack + [md.group(1)]) if stack else md.group(1)
                        out.append((str(path.relative_to(REPO)), full))
        if out:
            return out  # prefer Physlib over Mathlib
    return out


def main():
    tsv = Path(sys.argv[1])
    apply_mode = "--apply" in sys.argv
    fixes, visibility, ambiguous, missing, suspect = [], [], [], [], []
    seen = set()
    for line in tsv.read_text().splitlines():
        parts = line.split("\t")
        if len(parts) != 3:
            continue
        ref = parts[2].removeprefix("lean:")
        if ref in seen:
            continue
        seen.add(ref)
        short = ref.split(".")[-1]
        # every source root the environment carries — QuantumInfo is a sibling library,
        # and its declarations were the whole first-pass MISSING pile because the tokens
        # spell file paths (QuantumInfo.Entropy.X) while the real namespace is bare (X)
        cands = find_candidates(short, [REPO / "Physlib", REPO / "QuantumInfo",
                                        REPO / "PhyslibAlpha", MATHLIB])
        fulls = sorted({c[1] for c in cands})
        tail2_of_ref = ".".join(ref.split(".")[-2:])
        if ref in fulls:
            visibility.append(ref)
        elif len(fulls) == 1:
            # auto-apply only when the parent component survives the retarget;
            # a changed parent can be a name collision (MState.pure_apply vs
            # PMF.pure_apply), so it goes to manual triage instead
            if fulls[0].endswith(tail2_of_ref) or "." not in ref:
                fixes.append((ref, fulls[0]))
            else:
                suspect.append((ref, fulls[0]))
        elif len(fulls) == 0:
            missing.append(ref)
        else:
            # try suffix-disambiguation: candidate whose tail matches the ref's tail-2
            narrowed = [f for f in fulls if f.endswith(tail2_of_ref)]
            if len(narrowed) == 1:
                fixes.append((ref, narrowed[0]))
            else:
                ambiguous.append((ref, fulls[:4]))

    print(f"unique refs: {len(seen)}  FIX: {len(fixes)}  SUSPECT: {len(suspect)}"
          f"  VISIBILITY: {len(visibility)}"
          f"  AMBIGUOUS: {len(ambiguous)}  MISSING: {len(missing)}\n")
    for old, new in fixes:
        print(f"FIX\t{old}\n ->\t{new}")
    for old, new in suspect:
        print(f"SUSPECT\t{old}\n ?->\t{new}")
    for r in visibility:
        print(f"VISIBILITY\t{r}")
    for r, cs in ambiguous:
        print(f"AMBIGUOUS\t{r}\n  cands: {cs}")
    for r in missing:
        print(f"MISSING\t{r}")

    if apply_mode and fixes:
        n = 0
        for old, new in fixes:
            files = subprocess.run(
                ["grep", "-rl", f'lean:{old}"', str(REPO / "Physlib"), "--include=*.lean"],
                capture_output=True, text=True).stdout.split()
            for f in files:
                p = Path(f)
                txt = p.read_text(encoding="utf-8")
                p.write_text(txt.replace(f'lean:{old}"', f'lean:{new}"'), encoding="utf-8")
                n += 1
        print(f"\napplied {len(fixes)} fixes across {n} file-occurrences")


if __name__ == "__main__":
    main()
