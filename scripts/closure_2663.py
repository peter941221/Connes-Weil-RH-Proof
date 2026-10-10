#!/usr/bin/env python3
"""Transitive import-closure lister for the record-2663 build targets.

Usage: python scripts/closure_2663.py ConnesWeilRH.Dev.ModA [ModB ...]

Writes results/closure_2663.txt: repo-relative .lean paths of every
transitive `ConnesWeilRH.*` import of the given modules (the modules
themselves included), deduplicated, one per line.  Paths are relative to
the repository root with forward slashes, so the sync script can use them
verbatim under both the Windows tree and the WSL mirror.

Guards (house law: mirror import holes must surface at generation time):
a listed import that resolves to no file on disk is a hard error.
"""

import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

IMPORT_RE = re.compile(r"^import\s+(ConnesWeilRH[\w.]*)\s*$")


def module_file(mod):
    return os.path.join(ROOT, *mod.split(".")) + ".lean"


def imports_of(path):
    out = []
    with open(path, encoding="utf-8") as fh:
        in_block = False
        for line in fh:
            s = line.strip()
            if not s:
                continue
            if in_block:
                if "-/" in s:
                    in_block = False
                continue
            if s.startswith("/-"):
                if "-/" not in s:
                    in_block = True
                continue
            if s.startswith("--"):
                continue
            m = IMPORT_RE.match(s)
            if m:
                out.append(m.group(1))
                continue
            break
    return out


def main():
    mods = sys.argv[1:]
    if not mods:
        print("usage: closure_2663.py ConnesWeilRH.Dev.Mod ...")
        return 2
    seen = set()
    stack = list(mods)
    missing = []
    while stack:
        mod = stack.pop()
        if mod in seen:
            continue
        seen.add(mod)
        path = module_file(mod)
        if not os.path.exists(path):
            missing.append(mod)
            continue
        stack.extend(imports_of(path))
    if missing:
        for m in sorted(missing):
            print(f"ERROR missing module file: {m}")
        return 1
    rel = sorted(os.path.relpath(module_file(m), ROOT).replace("\\", "/")
                 for m in seen)
    out_path = os.path.join(ROOT, "results", "closure_2663.txt")
    os.makedirs(os.path.dirname(out_path), exist_ok=True)
    with open(out_path, "w", encoding="utf-8", newline="\n") as fh:
        fh.write("\n".join(rel) + "\n")
    print(f"closure: {len(rel)} files -> results/closure_2663.txt")
    return 0


if __name__ == "__main__":
    sys.exit(main())