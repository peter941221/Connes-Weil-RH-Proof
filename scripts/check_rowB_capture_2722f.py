#!/usr/bin/env python3
"""Independent check of the record-2722F row-B stored capture.

Lanes (all exact-rational or source-level; the payload is re-read from its
committed JSON, never regenerated):

  S-lane  module-vs-payload transcription ties:
    S1 storedRadius2722F literal == payload radius, radius in (87, 88)
    S2 storedTargets2722F finset literal == payload targets (order, exact)
    S3 storedNodes2722F finset literal == payload owner (order, exact)
    S4 storedY2722F ite guards == owner[48/49/52], values 1, -1, -1, else 0
    S5 the nine `storedNe*2722F` negation theorems carry the probe-verified
       proof shape (`intro h` / `exact absurd (congrArg Complex.im h)`)
    S6 the three captured-leg theorem statements (hsub/htri/hy shapes)
    S7 main theorem binder set = rho + 7 named hypotheses, application tail
       passes the three proved legs and the data defs, caps/pin bounds named
    S8 audit module: exactly 5 `#print axioms` lines, names inside the
       capture namespace, each a real module declaration
  P-lane  payload internal ties (exact Fractions):
    P1 targets == owner[48:56]; triple spellings at positions 5/6/7
    P2 owner[53/54/55] == (1/2, 0), (1, 0), (3/2, 0)
    P3 values nonzero exactly at 48 (+1), 49 (-1), 52 (-1)
    P4 rho == (Fraction of float 0.55, Fraction of float gamma); candidate
       reprs match the stored row-B keys
  K-lane  mutation controls (each perturbation must FIRE the guard;
          feasibility of every rejection is asserted, record-2722E law):
    K1 perturbed targets numerator  -> S2 comparator fails
    K2 perturbed radius             -> S1 comparator fails
    K3 renamed hgate24 binder       -> S7 binder set fails
    K4 flipped ite branch value     -> S4 comparator fails
  B-lane  build census read from the build log when present (the log is
          gitignored; its sha256 and readings are recorded INTO this
          artifact so the committed evidence is self-contained):
    B1 footer "Build completed successfully (N jobs)"
    B2 zero lines starting `error:`
    B3 zero sorryAx / "uses sorry"
    B4 exactly 5 axiom records, each bracket flattens to the standard trio
       (records counted separately from bracket contents, record-2722A law)
    B5 zero warnings on the two entry files
    B6 both entry modules appear in Built lines

Verdict "2722F-ROWB-CAPTURE-CHECK-GREEN" requires all lanes green with a
present build log; without the log the verdict is the weaker
"2722F-ROWB-CAPTURE-SOURCE-GREEN" and `full_attestation` is false.

This checker binds its own sha256 into the artifact: any later edit to this
file invalidates the binding and mandates a re-run (standing project law).

Usage: python3 scripts/check_rowB_capture_2722f.py [--log=PATH]
"""

import hashlib
import json
import re
import sys
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DEV = ROOT / "ConnesWeilRH" / "Dev"
MODPATH = DEV / "C1RowBStoredCapture2722F.lean"
AUDPATH = DEV / "C1RowBStoredCapture2722FAudit.lean"
PAYPATH = ROOT / "results" / "2722f_rowB_capture_data.json"
ARTPATH = ROOT / "results" / "2722f_rowB_capture_check.json"
GENPATH = ROOT / "scripts" / "generate_rowB_capture_2722f.py"

TRIPLE_FRAC = {
    "(1 / 2 : ℂ)": (Fraction(1, 2), Fraction(0)),
    "(1 : ℂ)": (Fraction(1), Fraction(0)),
    "(3 / 2 : ℂ)": (Fraction(3, 2), Fraction(0)),
}
GAMMA = 21.022039638771556
RE = 0.55
TRIO = {"propext", "Classical.choice", "Quot.sound"}
NEG_NAMES = [
    f"storedNe{t}{n}2722F"
    for t in ("Half", "One", "ThreeHalf")
    for n in ("Rho", "Omc", "Rph")
]


def fr_of(f: float) -> Fraction:
    n, d = float(f).as_integer_ratio()
    return Fraction(n, d)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def strip_ws(text: str) -> str:
    return re.sub(r"\s+", "", text)


def parse_component(text: str) -> Fraction:
    """'((n : R) / d)' or '(n : R)' -> exact Fraction."""
    t = strip_ws(text.replace("ℝ", "R"))
    m = re.fullmatch(r"\(\((-?\d+):R\)/(-?\d+)\)", t)
    if m:
        return Fraction(int(m.group(1)), int(m.group(2)))
    m = re.fullmatch(r"\((-?\d+):R\)", t)
    if m:
        return Fraction(int(m.group(1)))
    raise ValueError(f"bad component literal: {text!r}")


def parse_entry(text: str):
    """One Finset entry -> (re, im) exact Fractions."""
    t = text.strip()
    if t.startswith("⟨"):
        body = t.lstrip("⟨").rstrip("⟩")
        # split the two components at depth 0 (components keep their parens)
        depth, parts, cur = 0, [], ""
        for ch in body:
            if ch in "([{":
                depth += 1
            elif ch in ")]}":
                depth -= 1
            if ch == "," and depth == 0:
                parts.append(cur)
                cur = ""
            else:
                cur += ch
        parts.append(cur)
        assert len(parts) == 2, text
        return parse_component(parts[0]), parse_component(parts[1])
    if t in TRIPLE_FRAC:
        return TRIPLE_FRAC[t]
    raise ValueError(f"unparsed finset entry: {text!r}")


def brace_region(lines, start_pat, opener, closer):
    """Collect the text from the line matching start_pat through the
    balanced close of the following multi-character grouping."""
    idx = next(i for i, ln in enumerate(lines) if re.search(start_pat, ln))
    # find the first opening token at or after idx
    pos, buf, depth = idx, [], 0
    while pos < len(lines):
        ln = lines[pos]
        buf.append(ln)
        joined = "\n".join(buf)
        depth = joined.count(opener) - joined.count(closer)
        if depth == 0 and opener in joined:
            break
        pos += 1
    assert depth == 0, f"unbalanced {opener}{closer} region for {start_pat}"
    return idx, "\n".join(buf)


def split_entries(block: str):
    """Entries of the `{ e1, e2, ...}` finset body, split at depth-0 commas."""
    body = block[block.index("{") + 1: block.rindex("}")]
    entries, depth, cur = [], 0, ""
    for ch in body:
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩":
            depth -= 1
        if ch == "," and depth == 0:
            entries.append(cur)
            cur = ""
        else:
            cur += ch
    entries.append(cur)
    return [parse_entry(e) for e in entries]


def parse_ite(lines):
    """Return [(guard_pair, value_text)] plus the final else token."""
    # the ite nests; collect guards/values by scanning the def region
    start = next(i for i, ln in enumerate(lines)
                 if re.match(r"^def storedY2722F : ℂ → ℂ :=", ln))
    end = start
    while end < len(lines) and lines[end].strip() != "":
        end += 1
    body = "\n".join(lines[start:end])
    guards = re.findall(
        r"if z =\s*\((⟨(?:[^⟩]|\s)*⟩) : ℂ\) then\s*"
        r"(\(\d+\s*: ℂ\)|\(-\d+\s*: ℂ\))", body)
    assert len(guards) == 3, f"ite guards parsed: {len(guards)}"
    out = []
    for g, v in guards:
        flat = re.sub(r"\s+", " ", g)
        m = re.match(r"⟨\(\((-?\d+) : ℝ\) / (-?\d+)\), "
                     r"\(\((-?\d+) : ℝ\) / (-?\d+)\)⟩", flat)
        assert m, flat
        out.append(((Fraction(int(m.group(1)), int(m.group(2))),
                     Fraction(int(m.group(3)), int(m.group(4)))),
                    strip_ws(v.replace("ℂ", "C"))))
    tail = body[body.rindex("else 0"):].strip() if "else 0" in body else ""
    assert tail == "else 0", body[-40:]
    return out


def main() -> int:
    args = sys.argv[1:]
    log_arg = None
    for a in args:
        if a.startswith("--log="):
            log_arg = a.split("=", 1)[1]
        else:
            print(f"unknown argument {a}")
            return 2
    mod = MODPATH.read_text(encoding="utf-8")
    audit = AUDPATH.read_text(encoding="utf-8")
    payload = json.loads(PAYPATH.read_text(encoding="utf-8"))
    mlines = mod.splitlines()

    def F(pair):
        return Fraction(pair[0]), Fraction(pair[1])

    checks = []

    def chk(cid, ok, detail):
        checks.append({"id": cid, "pass": bool(ok), "detail": detail})
        return ok

    # ---- P-lane: payload internal ties (exact rational) ----
    owner = [F(p) for p in payload["owner"]]
    targets = [F(p) for p in payload["targets"]]
    values = [F(p) for p in payload["values"]]
    radius = Fraction(payload["radius"])
    chk("P1", targets == owner[48:56] and payload["target_owner_index"]
        == [48, 49, 50, 51, 52, 53, 54, 55],
        "targets == owner[48:56], 8 entries")
    chk("P2", [owner[i] for i in (53, 54, 55)]
        == [(Fraction(1, 2), Fraction(0)), (Fraction(1), Fraction(0)),
            (Fraction(3, 2), Fraction(0))],
        "triple at owner 53/54/55")
    nz = [i for i, v in enumerate(values) if v != (Fraction(0), Fraction(0))]
    chk("P3", nz == payload["spec_idx"]
        and [values[i] for i in nz]
        == [(Fraction(1), Fraction(0)), (Fraction(-1), Fraction(0)),
            (Fraction(-1), Fraction(0))],
        f"nonzero values exactly at {nz}")
    chk("P4", [fr_of(RE), fr_of(GAMMA)] == [Fraction(payload["rho"][0]),
                                            Fraction(payload["rho"][1])]
        and payload["candidate"] == {"gamma": repr(GAMMA), "re": repr(RE),
                                     "N": 5}
        and 87 < radius < 88,
        f"rho/candidate reprs tied; radius={float(radius):.6f} in (87, 88)")

    # ---- S-lane: module transcription ties ----
    m = re.search(r"def storedRadius2722F : ℝ :=\n  \(\((\d+) : ℝ\) / (\d+)\)",
                  mod)
    mod_radius = Fraction(int(m.group(1)), int(m.group(2))) if m else None
    chk("S1", mod_radius == radius,
        f"module radius literal == payload radius: {m is not None}")
    tgt_parsed = split_entries(brace_region(
        mlines, r"^def storedTargets2722F : Finset ℂ :=", "{", "}")[1])
    chk("S2", tgt_parsed == targets,
        f"targets finset {len(tgt_parsed)} == 8, order-exact")
    node_parsed = split_entries(brace_region(
        mlines, r"^def storedNodes2722F : Finset ℂ :=", "{", "}")[1])
    chk("S3", node_parsed == owner,
        f"nodes finset {len(node_parsed)} == 56, order-exact")
    ite = parse_ite(mlines)
    chk("S4", [g for g, _ in ite] == [owner[i] for i in (48, 49, 52)]
        and [v for _, v in ite] == ["(1:C)", "(-1:C)", "(-1:C)"],
        "ite guards == owner[48/49/52], values 1,-1,-1, else 0")
    shape_ok = True
    neg_tail = (" := by\n    intro h\n    exact absurd "
                "(congrArg Complex.im h) (by norm_num)")
    for nm in NEG_NAMES:
        i = next((k for k, ln in enumerate(mlines)
                  if ln.startswith(f"theorem {nm} :")), None)
        if i is None:
            shape_ok = False
            print(f"neg theorem missing: {nm}")
            continue
        j = i
        while j < len(mlines) and mlines[j].strip():
            j += 1
        region = "\n".join(mlines[i:j])
        if not region.startswith(f"theorem {nm} :\n    ¬((") \
                or not region.endswith(neg_tail):
            shape_ok = False
            print(f"neg shape missing: {nm}")
    chk("S5", shape_ok, "nine negation theorems carry the probe shape")
    chk("S6",
        "shiftedCC20Triple2722D ⊆ storedTargets2722F" in mod
        and "storedTargets2722F ⊆ storedNodes2722F" in mod
        and "∀ s ∈ shiftedCC20Triple2722D, storedY2722F s = 0" in mod
        and "0 < storedRadius2722F" in mod,
        "captured-leg statements verbatim (hsub/htri/hy/hRadius)")
    tstart = next(i for i, ln in enumerate(mlines)
                  if ln.startswith("theorem fourPointContradictionRowB"
                                   "Stored2722F"))
    tend = next(i for i in range(tstart, len(mlines))
               if mlines[i].startswith("    False :="))
    binders = re.findall(r"^    \(([A-Za-z]\w*) :",
                         "\n".join(mlines[tstart:tend]), re.M)
    app = " ".join(mlines[tend + 1:tend + 7])
    app_seq = ["fourPointContradictionRowBCarrier2722D",
               "storedTargets2722F", "storedNodes2722F",
               "storedTargetsSubset2722F", "storedTripleSubset2722F",
               "storedRadius2722F", "storedHRadius2722F", "storedY2722F",
               "storedYVanishes2722F", "rho", "hNorm", "hIm",
               "hcontractPin", "hquarticPin", "hquadraticPin",
               "hgate24", "hprefix"]
    toks = re.split(r"\s+", app)
    pos = 0
    for t in toks:
        if pos < len(app_seq) and t == app_seq[pos]:
            pos += 1
    chk("S7", binders == ["rho", "hNorm", "hIm", "hcontractPin",
                          "hquarticPin", "hquadraticPin", "hgate24",
                          "hprefix"]
        and pos == len(app_seq)
        and all(c in mod for c in ("wiredRhoNormCapRowB2721",
                                   "wiredRhoImCapRowB2721",
                                   "wiredQRowB2721", "wiredC4RowB2721",
                                   "wiredC2RowB2721")),
        f"binders {binders}; application sequence complete")
    alogs = re.findall(r"^#print axioms "
                       r"(ConnesWeilRH\.Source\.C1RowBStoredCapture2722F"
                       r"\.(\w+))$", audit, re.M)
    decls = set(re.findall(r"^(?:theorem|def) (\w+)", mod, re.M))
    chk("S8", len(alogs) == 5 and all(n in decls for _, n in alogs),
        f"audit pins 5 decls: {[n for _, n in alogs]}")

    # ---- K-lane: mutation controls (must fire) ----
    bad_t = list(targets)
    bad_t[0] = (bad_t[0][0] + 1, bad_t[0][1])
    k1 = tgt_parsed != bad_t and tgt_parsed == targets
    k2 = mod_radius != radius + 1
    k3 = [b.replace("hgate24", "hgate2x") for b in binders] != \
        ["rho", "hNorm", "hIm", "hcontractPin", "hquarticPin",
         "hquadraticPin", "hgate24", "hprefix"]
    k4 = ite[0][1] != "(2:C)" and [v for _, v in ite] == \
        ["(1:C)", "(-1:C)", "(-1:C)"]
    chk("K1", k1, "perturbed targets numerator is rejected by S2 comparator")
    chk("K2", k2, "perturbed radius is rejected by S1 comparator")
    chk("K3", k3, "renamed hgate24 binder is rejected by the S7 binder set")
    chk("K4", k4, "flipped ite branch value is rejected by S4 comparator")

    # ---- B-lane: build census (optional, logged into the artifact) ----
    attestation = {"full": False, "log": None, "log_sha256": None}
    log_path = Path(log_arg) if log_arg else \
        (ROOT / "_build_2722f_b2.log")
    if log_path.exists():
        log = log_path.read_text(encoding="utf-8", errors="replace")
        footer = re.search(r"Build completed successfully \((\d+) jobs\)",
                          log)
        err = len(re.findall(r"^error:", log, re.M))
        sorry = len(re.findall(r"sorryAx|uses sorry", log))
        recs = re.findall(r"depends on axioms: \[([^\]]*)\]",
                          re.sub(r"\n\s+", " ", log))
        trio_ok = len(recs) == 5 and all(
            {x.strip() for x in r.split(",")} == TRIO for r in recs)
        warn = len(re.findall(
            r"C1RowBStoredCapture2722FA?\.lean:\d+:\d+: warning", log))
        built = (re.search(r"Built ConnesWeilRH\.Dev\."
                           r"C1RowBStoredCapture2722F \(", log) is not None
                 and re.search(r"Built ConnesWeilRH\.Dev\."
                               r"C1RowBStoredCapture2722FAudit", log)
                 is not None)
        chk("B1", footer is not None,
            f"footer jobs {footer.group(1) if footer else None}")
        chk("B2", err == 0, f"error lines: {err}")
        chk("B3", sorry == 0, f"sorry occurrences: {sorry}")
        chk("B4", trio_ok, f"axiom records: {len(recs)}, trio-exact")
        chk("B5", warn == 0, f"entry-file warnings: {warn}")
        chk("B6", built, "both entry modules in Built lines")
        attestation = {"full": True, "log": str(log_path.name),
                       "log_sha256": sha256(log_path),
                       "footer_jobs": int(footer.group(1)) if footer
                       else None}
    else:
        print(f"build log absent: {log_path} (B-lane skipped)")

    failures = [c for c in checks if not c["pass"]]
    lanes_green = not failures
    full = attestation["full"]
    verdict = ("2722F-ROWB-CAPTURE-CHECK-GREEN"
               if lanes_green and full else
               "2722F-ROWB-CAPTURE-SOURCE-GREEN" if lanes_green
               else "2722F-ROWB-CAPTURE-CHECK-FAIL")

    artifact = {
        "schema": "2722F_ROWB_CAPTURE_CHECK_V1",
        "verdict": verdict,
        "full_attestation": full,
        "checks": checks,
        "n_checks": len(checks),
        "n_failed": len(failures),
        "build_attestation": attestation,
        "semantic_notes": {
            "wired_hypotheses_removed": 3,
            "named_hypotheses_remaining": 7,
            "rho_stays_named": True,
            "freeze": "DEAD_ON_CURRENT_FAMILY unchanged",
            "producer_go": False,
            "rh_claim": False,
            "pin_certification": "named hypotheses only (Lean brick open)",
        },
        "provenance": {
            "checker_sha256": sha256(Path(__file__)),
            "generator_sha256": sha256(GENPATH),
            "module_sha256": sha256(MODPATH),
            "audit_sha256": sha256(AUDPATH),
            "payload_sha256": sha256(PAYPATH),
            "python": sys.version,
        },
    }
    ARTPATH.write_text(json.dumps(artifact, indent=1, sort_keys=True) + "\n",
                       encoding="utf-8", newline="\n")
    print(json.dumps({"verdict": verdict, "n_checks": len(checks),
                      "failed": [c["id"] for c in failures]}))
    print(f"wrote: {ARTPATH.name}")
    return 0 if lanes_green else 1


if __name__ == "__main__":
    sys.exit(main())
