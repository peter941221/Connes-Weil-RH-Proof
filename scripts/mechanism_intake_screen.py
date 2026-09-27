#!/usr/bin/env python3
# mechanism_intake_screen.py — record 2050 (instrument, reusable)
#
# Keyword triage implementing the record-2047 antibody table at intake.
# Feed it a mechanism sketch (file(s) or stdin); it reports which antibody
# classes FIRE, with the ledger exhibit to read and the action to take.
#
# HONEST SCOPE: this is a triage aid over prose, not a decision procedure.
# Patterns fire on vocabulary; a fired class means "read the cited exhibit
# and check whether it applies", never "this mechanism is dead".  The
# verdict always comes from the exhibit, not from this script.
#
# Usage:
#   python3 scripts/mechanism_intake_screen.py NOTES.md [NOTES2.md ...]
#   cat sketch.txt | python3 scripts/mechanism_intake_screen.py -
#   ... [--json results/2050_intake_screen_demo.json]

import json
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# (class, firing rule, regex patterns, exhibits, action)
SCREEN = [
    ("SPLIT",
     "rewrites the target as an identity split A = A1 + A2 whose remainder "
     "is forced by the same sign",
     [r"\bidentity split", r"\bsplitting\b", r"\bdecompos\w+ the (target|form)",
      r"sign conserv", r"remainder .{0,30}same sign"],
     "F82 / record 2039 (sign conservation under identity splitting); "
     "record 1341 (family choice adds no strength)",
     "check whether the split is F82-style (sign-preserving) before pricing"),
    ("PRE",
     "the hypothesis imports the conclusion or an RH-equivalent premise",
     [r"assum\w+ the (Riemann hypothesis|RH)", r"RH-equivalent",
      r"equivalent to (RH|the Riemann hypothesis)",
      r"conditioned on (RH|the Riemann)", r"assum\w+ .{0,20}positivity of the (Weil|explicit) form"],
     "record 1995 (Velez stabilization audit); map 095-102 (generic "
     "conditional exits FROZEN)",
     "factor the imported premise out; if the theorem is conditional, it "
     "cannot move the mainline"),
    ("CHAN",
     "the imported dictionary speaks about the wrong side / channel",
     [r"\bdictionary\b", r"\banalogue (of|to)\b", r"\bchannel\b",
      r"transport .{0,25}(other|different) (side|problem)"],
     "record 2042 (Helson: the prime channel is already positive-definite "
     "by construction); record 1055 (prolate: amplifier output)",
     "name the side/channel the import speaks about and verify it is the "
     "owner's"),
    ("IND",
     "gate index and tail-closure index are disjoint / shifted",
     [r"gate index", r"tail.{0,15}index", r"\bdisjoint index",
      r"closes? at n = ", r"index mismatch"],
     "record 2035 (Route B: admissible gate rows exist, the same-index tail "
     "closes one step later where the gate is gone)",
     "compute both indices on the actual family before any pricing"),
    ("TRUNC",
     "a structure verdict is read on a truncated book / lattice",
     [r"\btruncat", r"\bfinite section\b", r"cut(s|ting)? (it |the book )?off",
      r"\bsmoke\b"],
     "record 2044 (truncated-lattice smoke manufactured normality 2.45e-4; "
     "complete book r-GENERIC 0.7215)",
     "re-read the structure verdict on the COMPLETE book"),
    ("STAB",
     "the 'pinned' quantity is not stable in the family parameter it is "
     "claimed in",
     [r"\bpinn", r"\bstab\w* in\b", r"family parameter", r"\bmonotone in\b"],
     "record 1063 (raw F1: the nonmeet sum grows with K; only the "
     "D-weighted F1' survives)",
     "vary the family parameter; keep only functionals stable under it"),
    ("TEST",
     "no certificate can even falsify the claim",
     [r"not falsifiable", r"unfalsifiable", r"no certificate",
      r"not provable and not falsifiable"],
     "record 1055 (semilocal P2b probe)",
     "design a falsification window first; an unfalsifiable claim is not a "
     "mechanism"),
    ("VAC",
     "the hypothesis holds where the conclusion is known/trivial, or would "
     "prove a false analogue",
     [r"\bvacuous", r"small window", r"\btrivial(ly)?\b",
      r"false analogue", r"would prove too much"],
     "record 1411 (radius shrink: positivity holds in small windows - "
     "target vacuous there); DH and RT below",
     "check the mechanism on a Riemann-type function with off-line zeros "
     "(DH) and check whether it needs slack (RT)"),
    ("GAP",
     "the imported theorem's error term provably exceeds the margin",
     [r"error term", r"epsilon-gap", r"eps-gap", r"error .{0,15}exceeds",
      r"\bmargin\b"],
     "records 1590-1634 (carrier/Toeplitz/Makarov-Poltoratski lane: "
     "eps-gap closure, laws F48-F58)",
     "compare the error exponent with the margin exponent explicitly"),
    ("INDEF",
     "the mechanism needs a sign from an operator that is provably "
     "indefinite",
     [r"\bindefinite\b", r"not positive definite",
      r"sign of .{0,20}compression", r"negative index"],
     "record 2045 NO-GO-OPERATOR-SIGN (A = P-Q indefinite whenever "
     "[P,u] != 0); NO-GO-CORNER (defect block [[0,B],[B^T,C]], B != 0)",
     "abandon operator-level sign mechanisms; the sign must come from the "
     "VECTOR"),
    ("DH",
     "the hypotheses are met by Riemann-type functions with a functional "
     "equation but off-line zeros (FE-alone stowaway)",
     [r"functional equation only", r"FE-only", r"\bFE alone\b",
      r"Davenport-Heilbronn", r"universality of the functional equation",
      r"same functional equation", r"any (function|L-function) with .{0,25}"
      r"functional equation"],
     "record 2047 section 3 (Davenport-Heilbronn 1936)",
     "identify the extra input beyond the functional equation, or drop the "
     "mechanism"),
    ("RT",
     "the mechanism needs a positive margin / slack that a Lambda >= 0 "
     "theorem forbids",
     [r"positive margin", r"\bslack\b", r"improve the constant",
      r"de Bruijn-Newman", r"Rodgers-Tao", r"with room to spare"],
     "record 2047 section 3 (Rodgers-Tao, arXiv 1801.05914)",
     "at the correct time parameter the inequality must be tight/exact: "
     "either identity-exact or dead"),
]


def ascii_safe(s):
    return s.encode("ascii", "replace").decode("ascii")


# Self-contained demonstration candidates (--demo): short synthetic sketches
# plus the two live 2026-09-27 candidates, so the tool is reproducible with
# no temp files and no local paths in the artifact.
DEMO = [
    ("demo: FE-only stowaway",
     "Candidate: use the functional equation of the completed zeta function "
     "and a positivity of the explicit form to conclude.  We assume the "
     "Riemann hypothesis on a small window and note the positivity holds in "
     "small windows, so the target is vacuous there; the mechanism should "
     "work for any function with the same functional equation."),
    ("demo: compression-sign",
     "Candidate: read the sign of the kernel from the compression of the "
     "Weil form; the negative index of the truncated operator is nonzero, so "
     "the operator is indefinite and some direction is negative."),
    ("demo: panel-local model (record 2046 section 4)",
     "Candidate: enclose g, not the kernel, on a uniform panel grid; the "
     "panelwise linear model is integrated against the book in closed form "
     "and only the interpolation remainder is charged, by the crude bound "
     "(h^2/8) sup|g''| per panel.  The nodal values carry interval "
     "enclosures; the charge is a function of h alone."),
]


def screen_text(name, text):
    rows = []
    for cls, rule, patterns, exhibits, action in SCREEN:
        snippets = []
        for pat in patterns:
            for m in re.finditer(pat, text, re.IGNORECASE):
                a = max(0, m.start() - 40)
                b = min(len(text), m.end() + 40)
                snippets.append(text[a:b].replace("\n", " "))
                if len(snippets) >= 3:
                    break
            if len(snippets) >= 3:
                break
        if snippets:
            rows.append({"class": cls, "rule": rule, "exhibits": exhibits,
                         "action": action, "snippets": snippets})
    return {"input": name, "fired": rows}


def main():
    args = []
    out_path = None
    demo = False
    argv = sys.argv[1:]
    i = 0
    while i < len(argv):
        a = argv[i]
        if a == "--json":
            out_path = argv[i + 1]
            i += 2
            continue
        if a == "--demo":
            demo = True
            i += 1
            continue
        args.append(a)
        i += 1
    if demo:
        args = args + ["<demo:%d>" % i for i in range(len(DEMO))]
    if not args:
        print(__doc__)
        return 1
    results = []
    for arg in args:
        if arg == "-":
            text = sys.stdin.read()
            name = "<stdin>"
        elif arg.startswith("<demo:"):
            idx = int(arg[6:-1])
            name, text = DEMO[idx]
        else:
            with open(arg, encoding="utf-8", errors="replace") as f:
                text = f.read()
            name = os.path.relpath(os.path.abspath(arg), ROOT).replace("\\", "/")
        res = screen_text(name, text)
        results.append(res)
        print("== %s : %d class(es) fired" % (name, len(res["fired"])))
        for r in res["fired"]:
            print("   %-6s %s" % (r["class"], r["rule"]))
            print("          exhibits: %s" % ascii_safe(r["exhibits"]))
            for s in r["snippets"][:2]:
                print("          hit: ...%s..." % ascii_safe(s.strip()[:100]))
    if out_path:
        with open(out_path, "w", encoding="utf-8", newline="\n") as f:
            json.dump({"record": 2050, "screen": [
                {"class": c_, "rule": r_, "exhibits": e_, "action": a_}
                for c_, r_, _p, e_, a_ in SCREEN], "results": results},
                f, indent=2)
            f.write("\n")
        print("RESULT", out_path)
    return 0


if __name__ == "__main__":
    sys.exit(main())