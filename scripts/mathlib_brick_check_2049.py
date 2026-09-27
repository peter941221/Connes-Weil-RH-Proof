#!/usr/bin/env python3
# mathlib_brick_check_2049.py — record 2049 (instrument, reusable)
#
# Toolchain-brick availability check against the PINNED mathlib tree.
# Table-driven: each row is (brick name, list of regex patterns, note).
# For every brick the checker greps .lake/packages/mathlib/Mathlib/**/*.lean
# and reports PRESENT (with file:line of the first matches) or ABSENT.
#
# This is the evidence tool for record-2045 kill condition 4 (the neighbor
# paper's claimed mathlib bricks) and a general instrument for any future
# Lean-side plan that rests on "mathlib has X".
#
# Usage:  python3 scripts/mathlib_brick_check_2049.py [--json path]
# Output: results/2049_mathlib_brick_check.json (+ stdout summary)

import json
import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
MATHLIB = os.path.join(ROOT, ".lake", "packages", "mathlib")

# (brick, [regex patterns], note)
BRICKS = [
    ("sylvester_inertia_uniqueness",
     [r"sigPos_eq", r"sigNeg_eq"],
     "congruence invariance of the inertia indices (uniqueness half of "
     "Sylvester's law of inertia), real quadratic forms"),
    ("sylvester_inertia_existence",
     [r"equivalent_one_neg_one_weighted_sum_squared"],
     "existence half: a nondegenerate real quadratic form is equivalent to "
     "a weighted sum of squares with +-1 weights"),
    ("birkhoff_von_neumann",
     [r"doublyStochastic_eq_convexHull_permMatrix",
      r"exists_eq_sum_perm_of_mem_doublyStochastic"],
     "Birkhoff's theorem: doubly stochastic = convex hull of permutation "
     "matrices (the rearrangement engine)"),
    ("rearrangement_inequality",
     [r"Monovary.*sum_smul_comp_perm_le_sum_smul",
      r"Antivary.*sum_smul_le_sum_smul_comp_perm"],
     "Hardy-Littlewood-Polya rearrangement: aligned pairing maximizes the "
     "sum of products"),
    ("hermitian_trace_eq_sum_eigenvalues",
     [r"trace_eq_sum_eigenvalues"],
     "tr A = sum of eigenvalues for Hermitian A (spectral trace identity)"),
    ("singular_values_api",
     [r"noncomputable def singularValues", r"singularValues_antitone"],
     "singular values of a linear map between inner product spaces"),
    ("von_neumann_trace_inequality",
     [r"\btrace_mul_le\b(?!_left|_right)", r"\btrace\w*_le\w*singular",
      r"\bsingularValues\w*_trace\b", r"\bvonNeumann\w*trace\b",
      r"\btrace\w*vonNeumann\b"],
     "the NAMED theorem |tr(AB)| <= sum sigma_i(A) sigma_i(B) - expected "
     "ABSENT; the three proof ingredients above are all present.  NOTE: "
     "patterns must be word-boundary anchored - an unanchored "
     "'trace_mul_le' matches the unrelated Matrix.ext_iff_trace_mul_left"),
]


def mathlib_rev():
    try:
        out = subprocess.run(["git", "rev-parse", "HEAD"], cwd=MATHLIB,
                             capture_output=True, text=True, timeout=60)
        return out.stdout.strip() or None
    except Exception:
        return None


def grep_mathlib_all(bricks):
    """Single walk over the mathlib tree; for each brick collect up to 3
    (file, line, text) evidence rows over all of its patterns."""
    p = os.path.join(MATHLIB, "Mathlib")
    compiled = [(name, [re.compile(pat) for pat in patterns])
                for name, patterns, _note in bricks]
    hits = {name: [] for name, _patterns, _note in bricks}
    for dirpath, _dirnames, filenames in os.walk(p):
        for fn in filenames:
            if not fn.endswith(".lean"):
                continue
            fp = os.path.join(dirpath, fn)
            rel = os.path.relpath(fp, ROOT).replace("\\", "/")
            try:
                with open(fp, encoding="utf-8", errors="replace") as f:
                    for i, line in enumerate(f, 1):
                        for name, pats in compiled:
                            if len(hits[name]) >= 3:
                                continue
                            if any(pat.search(line) for pat in pats):
                                hits[name].append([rel, i, line.strip()[:160]])
            except OSError:
                continue
    return hits


def ascii_safe(s):
    """Windows consoles here are GBK; mathlib source is full of Unicode
    (blackboard-bold, arrows).  Keep stdout printable without touching the
    JSON (which is UTF-8 by construction)."""
    return s.encode("ascii", "replace").decode("ascii")


def main():
    if not os.path.isdir(os.path.join(MATHLIB, "Mathlib")):
        print("mathlib tree not found at", MATHLIB)
        return 1
    toolchain = None
    tc = os.path.join(ROOT, "lean-toolchain")
    if os.path.isfile(tc):
        with open(tc, encoding="utf-8") as f:
            toolchain = f.read().strip()
    out = {"record": 2049, "mathlib_rev": mathlib_rev(),
           "toolchain": toolchain, "rows": []}
    all_hits = grep_mathlib_all(BRICKS)
    for name, patterns, note in BRICKS:
        hits = all_hits[name]
        present = bool(hits)
        out["rows"].append({"brick": name, "present": present,
                            "note": note,
                            "evidence": hits[:3]})
        print("%-32s %s" % (name, "PRESENT" if present else "ABSENT"))
        for rel, ln, txt in hits[:2]:
            print("    %s:%d  %s" % (rel, ln, ascii_safe(txt[:110])))
    path = os.path.join(ROOT, "results", "2049_mathlib_brick_check.json")
    for i, arg in enumerate(sys.argv):
        if arg == "--json":
            path = sys.argv[i + 1]
    with open(path, "w", encoding="utf-8", newline="\n") as f:
        json.dump(out, f, indent=2)
        f.write("\n")
    print("RESULT", path)
    return 0


if __name__ == "__main__":
    sys.exit(main())