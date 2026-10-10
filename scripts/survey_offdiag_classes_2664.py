#!/usr/bin/env python3
"""Record 2664 scoping: exact (radius, beta, psi) parameter classes of the
900 owner-moment entries.

The record-2624/2655-2663 per-panel Lean chain depends on the entry only
through the exact triple

    radius_j = width_j^2,
    beta_ij  = Re(node_i) * radius_j,
    psi_ij   = (Im(node_i) + modulation_j) * radius_j

(the capture has modulation_j = -Im(node_j), so psi is the height gap times
the column radius).  This probe computes all 900 triples in exact rational
arithmetic from the committed capture, verifies the class hypothesis
(nodes 0/1/4, 2/3, 5/6/7 coincide exactly; likewise the captured families),
and reports the distinct-triple partition with representatives.

If two entries share a triple, THE ENTIRE per-panel chain is shareable:
tables, analytic certificates, amp/phase pins, true balls and the 13 support
modules are class-level; only the 2597 home rectangle and the final four
barrier inequalities are entry-level.  Output: results/2664_offdiag_classes.json.
Data layer only: no Lean modules, no membership claim.
"""

import hashlib
import json
import sys
from fractions import Fraction as F
from pathlib import Path

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)

ROOT = Path(__file__).resolve().parents[1]


def load_capture():
    return json.loads(
        (ROOT / "results/2275_gap_owner_audit.json").read_text()
    )["owner_capture"]


def exact_pairs(capture):
    nodes = [tuple(F(float.fromhex(v)) for v in hx)
             for hx in capture["nodes_hex"]]
    fams = [tuple(F(float.fromhex(v)) for v in hx)
            for hx in capture["families_hex"]]
    return nodes, fams


def entry_triple(nodes, fams, row, column):
    width, modulation = fams[column]
    node_re, node_im = nodes[row]
    radius = width * width
    return (radius, node_re * radius, (node_im + modulation) * radius)


def main():
    capture = load_capture()
    nodes, fams = exact_pairs(capture)

    # ---- class hypothesis: exact pair coincidences ----
    def groups(items):
        out = {}
        for idx, item in enumerate(items):
            out.setdefault(item, []).append(idx)
        return sorted((sorted(g) for g in out.values()),
                      key=lambda g: g[0])

    node_groups = groups(nodes)
    family_groups = groups(fams)

    classes = {}
    for row in range(30):
        for column in range(30):
            triple = entry_triple(nodes, fams, row, column)
            classes.setdefault(triple, []).append((row, column))

    members = sorted(classes.items(), key=lambda kv: kv[1][0])

    def is_diag(pair):
        return pair[0] == pair[1]

    def offdiag_members(triple):
        return [p for p in classes[triple] if not is_diag(p)]

    offdiag_classes = [(t, m) for t, m in members if offdiag_members(t)]
    diag_only = [(t, m) for t, m in members if not offdiag_members(t)]

    def describe(triple):
        radius, beta, psi = triple
        return {
            "radius_exact": str(radius),
            "beta_exact": str(beta),
            "psi_exact": str(psi),
            "abs_psi_float": float(abs(psi)),
            "psi_zero": psi == 0,
            "representative": list(min(offdiag_members(triple))),
            "offdiag_members": [list(p) for p in sorted(offdiag_members(triple))],
            "diagonal_members": [list(p) for p in sorted(classes[triple])
                                 if is_diag(p)],
            "offdiag_size": len(offdiag_members(triple)),
            "total_size": len(classes[triple]),
        }

    offdiag_entries = sum(len(offdiag_members(t)) for t, _ in offdiag_classes)
    assert offdiag_entries == 30 * 29
    chains_new = [t for t, _ in offdiag_classes
                  if offdiag_members(t) != [(0, 3)]]
    payload = {
        "record": 2664,
        "purpose": "exact parameter-class partition of the 900 entry triples",
        "node_groups": node_groups,
        "family_groups": family_groups,
        "summary": {
            "distinct_triples_all_900": len(classes),
            "offdiagonal_entries": offdiag_entries,
            "offdiag_classes_needing_new_lean_chain": len(chains_new),
            "offdiag_classes_with_committed_chain": len(offdiag_classes)
                                                    - len(chains_new),
            "offdiagonal_entries_per_class": round(
                offdiag_entries / len(offdiag_classes), 3),
            "max_offdiag_members_in_one_class":
                max(len(offdiag_members(t)) for t, _ in offdiag_classes),
            "class_size_histogram": _hist(len(m) for _, m in members),
            "psi_zero_offdiag_entries": offdiag_entries - sum(
                len(offdiag_members(t)) for t, _ in offdiag_classes
                if t[2] != 0),
            "committed_diag_22_class_members":
                [list(p) for p in classes[
                    next(t for t, m in members if len(m) == 22)]],
            "diag_only_classes": len(diag_only),
        },
        "offdiag_classes": [describe(t) for t, _ in offdiag_classes],
        "generator_sha256": hashlib.sha256(
            Path(__file__).read_bytes()).hexdigest(),
        "capture_sha256": hashlib.sha256(
            (ROOT / "results/2275_gap_owner_audit.json").read_bytes()
        ).hexdigest(),
        "membership_claimed": False, "producer_go": False, "rh_claim": False,
    }
    out = ROOT / "results/2664_offdiag_classes.json"
    out.write_text(json.dumps(payload, indent=1) + "\n",
                   encoding="utf-8", newline="\n")

    print(f"node groups:   {node_groups}")
    print(f"family groups: {family_groups}")
    s = payload["summary"]
    print(f"distinct triples over 900 entries: {s['distinct_triples_all_900']}")
    print(f"offdiag entries / classes: {s['offdiagonal_entries']} / "
          f"{len(payload['offdiag_classes'])} "
          f"(max members in one class: "
          f"{s['max_offdiag_members_in_one_class']})")
    print(f"offdiag classes needing a new chain: "
          f"{s['offdiag_classes_needing_new_lean_chain']}")
    print(f"class sizes: {s['class_size_histogram']}")
    print(f"psi=0 offdiag entries: {s['psi_zero_offdiag_entries']}")
    print(f"wrote {out.name}")
    return 0


def _hist(values):
    out = {}
    for v in values:
        out[str(v)] = out.get(str(v), 0) + 1
    return out


if __name__ == "__main__":
    sys.exit(main())