#!/usr/bin/env python3
"""Record 2723 checker: the hprefix -> orbit-data replacement, transcription
guards, mutation controls, and the build/axiom census.

Canonical sources are read relative to the repository root (this script's
parent directory), so the checker is location-independent.  The build
evidence lives in the Linux workspace and is passed in:

    python3 scripts/check_rowB_prefix_2723.py [--log=PATH] [--mirror=PATH]

`--log` is the lake build log; `--mirror` is the Linux workspace holding the
built modules and oleans.  Without them the verdict is the weaker
source-only grade and the artifact states which lanes were skipped.  The
artifact records the checker's own sha256: any later edit to this script
invalidates the binding and mandates a re-run.
"""

import hashlib
import io
import json
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DEV = "ConnesWeilRH/Dev/C1RowBPrefixTransport2723.lean"
AUDIT = "ConnesWeilRH/Dev/C1RowBPrefixTransport2723Audit.lean"
PARENT = "ConnesWeilRH/Dev/C1RowBStoredCapture2722F.lean"
OUT = os.path.join(ROOT, "results", "2723_rowB_prefix_check.json")

NS = "ConnesWeilRH.Source.C1RowBPrefixTransport2723."
THEOREMS = [
    "dyadicShellIndex_abs_im_lt_six_2723",
    "rowBSpanPrefix_re_le_negXiMult_sq_2723",
    "rowBSpanPrefix_of_imCap_2723",
    "storedRowBPrefix2723",
    "fourPointContradictionRowBStored2723",
]
PARENT_BINDERS = [
    "rho", "hNorm", "hIm", "hcontractPin", "hquarticPin", "hquadraticPin",
    "hgate24", "hprefix",
]
VARIANT_BINDERS = [
    "rho", "hNorm", "hIm", "hright", "hcontractPin", "hquarticPin",
    "hquadraticPin", "hgate24", "htarget", "hzero",
]
AXIOM_TRIO = {"propext", "Classical.choice", "Quot.sound"}

SUM_RE = re.compile(
    r"\(∑ k ∈ Finset\.range 6, ∑' z : spectralHeightShell k,.*?"
    r"\* 24 \^ 2(?=[)])",
    re.S,
)
APPLY_RE = re.compile(
    r"fourPointContradictionRowBStored2722F rho hNorm hIm"
    r".*?\(storedRowBPrefix2723 rho hright hIm htarget hzero\)",
    re.S,
)
APPLY_SHAPE = (
    "fourPointContradictionRowBStored2722F rho hNorm hIm "
    "hcontractPin hquarticPin hquadraticPin hgate24 "
    "(storedRowBPrefix2723 rho hright hIm htarget hzero)"
)

results = []
failures = []


def check(name, ok, detail=""):
    results.append({"check": name, "ok": bool(ok), "detail": detail})
    if not ok:
        failures.append(name)
    return ok


def norm(text):
    return " ".join(text.split())


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 16), b""):
            h.update(chunk)
    return h.hexdigest()


def read(path):
    with io.open(path, encoding="utf-8") as handle:
        return handle.read()


def binder_list(module_text, theorem_name):
    start = module_text.index("theorem " + theorem_name)
    end = module_text.index("False :=", start)
    region = module_text[start:end]
    return re.findall(r"\((h[A-Za-z0-9]+|rho) :", region)


def main():
    log_arg = None
    mirror = None
    for arg in sys.argv[1:]:
        if arg.startswith("--log="):
            log_arg = arg.split("=", 1)[1]
        elif arg.startswith("--mirror="):
            mirror = arg.split("=", 1)[1]

    dev_path = os.path.join(ROOT, DEV)
    audit_path = os.path.join(ROOT, AUDIT)
    parent_path = os.path.join(ROOT, PARENT)
    for path in (dev_path, audit_path, parent_path):
        if not check("exists:" + os.path.basename(path), os.path.exists(path),
                     os.path.relpath(path, ROOT)):
            return finish()

    dev = read(dev_path)
    audit = read(audit_path)
    parent = read(parent_path)

    # P1: optional mirror byte-identity (the built bytes are the canonical
    # bytes).  Skipped without --mirror; recorded as skipped.
    if mirror:
        for tag, rel in (("dev", DEV), ("audit", AUDIT)):
            mpath = os.path.join(mirror, rel)
            check("P1." + tag + ".mirror_sha256",
                  os.path.exists(mpath)
                  and sha256_file(mpath) == sha256_file(
                      os.path.join(ROOT, rel)))
    else:
        results.append({"check": "P1.mirror_sha256", "ok": True,
                        "detail": "SKIPPED (no --mirror)"})

    # P2: the five theorem names, boundary-anchored at line granularity.
    for name in THEOREMS:
        pattern = re.compile(r"^theorem " + name + r"\b", re.M)
        check("P2.theorem:" + name, bool(pattern.search(dev)))

    # P3: the audit's exact #print axioms call list.
    wanted = ["#print axioms " + NS + name for name in THEOREMS]
    got = [line.strip() for line in audit.splitlines()
           if line.strip().startswith("#print axioms")]
    check("P3.audit_print_list", got == wanted, "got=" + repr(got))

    # P4: binder lists (parent and variant) pinned to the committed text.
    pb = binder_list(parent, "fourPointContradictionRowBStored2722F")
    vb = binder_list(dev, "fourPointContradictionRowBStored2723")
    check("P4.parent_binders", pb == PARENT_BINDERS, "got=" + repr(pb))
    check("P4.variant_binders", vb == VARIANT_BINDERS, "got=" + repr(vb))

    # P5: the variant's positional application of the parent: 8-argument
    # prefix plus the stored prefix witness as the last argument.
    m = APPLY_RE.search(dev)
    check("P5.parent_application", bool(m))
    if m:
        check("P5.application_shape", norm(m.group(0)) == APPLY_SHAPE,
              norm(m.group(0)))

    # P6: the hprefix token tie between the parent hypothesis and the 2723
    # stored conclusion (whitespace-normalized token stream).
    parent_sum = SUM_RE.findall(parent)
    stored_sum = [t for t in SUM_RE.findall(dev)
                  if "storedCarrierSourceTest2722F" in t]
    check("P6.parent_sum_count", len(parent_sum) == 1,
          "count=" + str(len(parent_sum)))
    check("P6.stored_sum_count", len(stored_sum) == 1,
          "count=" + str(len(stored_sum)))
    if len(parent_sum) == 1 and len(stored_sum) == 1:
        check("P6.hprefix_token_tie",
              norm(parent_sum[0]) == norm(stored_sum[0]))

    # K-lane: mutation controls (each must be rejected by its guard).
    k1 = re.sub(r"(fourPointContradictionRowBStored2722F rho )hNorm hIm",
                r"\1hIm hNorm", dev)
    check("K1.swapped_caps_rejected",
          k1 != dev and not APPLY_RE.search(k1),
          "mutated=" + str(k1 != dev))
    k2 = audit.replace("#print axioms " + NS + THEOREMS[0] + "\n", "")
    got2 = [l.strip() for l in k2.splitlines()
            if l.strip().startswith("#print axioms")]
    check("K2.dropped_print_rejected", got2 != wanted)
    k3 = re.sub(r"\(hright : \(1 / 2 : Real\) < rho\.1\.re\)\n", "", dev)
    check("K3.dropped_hright_rejected",
          k3 != dev
          and binder_list(k3, "fourPointContradictionRowBStored2723")
          != VARIANT_BINDERS,
          "mutated=" + str(k3 != dev))
    k4 = dev.replace(
        "(storedCarrierSourceTest2722F) 24).convolutionSquare",
        "(storedCarrierSourceTest2722F) 23).convolutionSquare")
    s4 = [t for t in SUM_RE.findall(k4)
          if "storedCarrierSourceTest2722F" in t]
    check("K4.order_flip_rejected",
          k4 != dev
          and not (len(s4) == 1 and len(parent_sum) == 1
                   and norm(s4[0]) == norm(parent_sum[0])),
          "mutated=" + str(k4 != dev))

    # B-lane: build evidence from the log (optional).
    attestation = {
        "full": False,
        "log_basename": os.path.basename(log_arg) if log_arg else None,
        "log_sha256": None,
    }
    if log_arg and os.path.exists(log_arg):
        log_text = read(log_arg)
        attestation["log_sha256"] = sha256_file(log_arg)
        check("B1.footer", "Build completed successfully" in log_text)
        check("B1.error_lines",
              len(re.findall(r"^error:", log_text, re.M)) == 0)
        check("B1.sorry_lines",
              len(re.findall(r"uses sorry|sorryAx", log_text)) == 0)
        records = re.findall(r"depends on axioms: \[(.*?)\]", log_text, re.S)
        trios_ok = all(
            {t.strip() for t in rec.replace("\n", " ").split(",")}
            == AXIOM_TRIO for rec in records)
        check("B1.axiom_records", len(records) == 5 and trios_ok,
              "count=" + str(len(records)))
        warn = [l for l in log_text.splitlines()
                if "warning" in l and "C1RowBPrefixTransport2723" in l]
        check("B2.entry_warning_free", not warn, "|".join(warn[:3]))
        attestation["full"] = True
        if mirror:
            for tag, name in (
                    ("dev", "C1RowBPrefixTransport2723.olean"),
                    ("audit", "C1RowBPrefixTransport2723Audit.olean")):
                opath = os.path.join(
                    mirror, ".lake/build/lib/lean/ConnesWeilRH/Dev", name)
                check("B3.olean:" + tag, os.path.exists(opath),
                      str(os.path.getsize(opath))
                      if os.path.exists(opath) else "missing")
    else:
        results.append({"check": "B1.census", "ok": True,
                        "detail": "SKIPPED (no --log)"})

    return finish(attestation)


def finish(attestation=None):
    artifact = {
        "schema": "2723_ROWB_PREFIX_CHECK_V1",
        "verdict": "GREEN" if not failures else "FAIL",
        "grade": ("build-attested" if attestation and attestation["full"]
                  else "source-only"),
        "failures": failures,
        "checks_passed": len(results) - len(failures),
        "checks_total": len(results),
        "results": results,
        "attestation": attestation or {},
        "premise_accounting": {
            "parent_premises": PARENT_BINDERS[1:],
            "variant_premises": VARIANT_BINDERS[1:],
            "removed": ["hprefix"],
            "added": ["hright", "htarget", "hzero"],
            "honesty": ("hprefix was an analytic sign estimate; the "
                        "replacements are pointwise orbit-data facts, and the "
                        "summation sign argument now lives in the proved "
                        "record-2722C transport theorem. Count grows, kind "
                        "shrinks."),
        },
        "provenance": {
            "checker_sha256": sha256_file(os.path.abspath(__file__)),
            "dev_sha256": sha256_file(os.path.join(ROOT, DEV)),
            "audit_sha256": sha256_file(os.path.join(ROOT, AUDIT)),
        },
    }
    with io.open(OUT, "w", encoding="utf-8", newline="\n") as handle:
        json.dump(artifact, handle, indent=2, ensure_ascii=True)
        handle.write("\n")
    print("VERDICT:", artifact["verdict"], artifact["grade"],
          artifact["checks_passed"], "/", artifact["checks_total"])
    if failures:
        print("FAILURES:", failures)
    return 0 if not failures else 1


if __name__ == "__main__":
    sys.exit(main())