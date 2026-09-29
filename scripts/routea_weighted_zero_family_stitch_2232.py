"""Record 2232: family-stitch closure by directed re-accumulation.

The 2229 node total was stitched in binary64 (`total = nextafter-up(total +
gl + sim)`).  This record closes that stitch with a two-part argument:

  lemma: gl and sim are MPFR-RNDU rounded to binary64, hence upward of the
  exact family charges.  In `c2 = fl(fl(T + gl) + sim)` each of the two
  roundings is at most half a spacing of the result downward, so
  `c2 >= T + gl + sim - spacing(c2)`; the single `nextafter` step upward
  adds exactly one spacing, so the stitch is outward (non-strict).

  verification: re-accumulate the committed per-family rows with MPFR RNDU
  (256-bit) and check that every reported 2229 node total is at least the
  directed re-accumulation, with the deficit bounded by the lemma.

Reads results/2229_q_mpfr_node*.json, writes
results/2232_family_stitch_closure.json.
"""
import ctypes as C
import importlib.util
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
R = ROOT / "results"


def _load(name, filename):
    sp = importlib.util.spec_from_file_location(name, ROOT / "scripts" / filename)
    mod = importlib.util.module_from_spec(sp)
    sp.loader.exec_module(mod)
    return mod


m = _load("mpfr2232", "routea_weighted_zero_mpfr_exp_binding_2223.py")
lib = m._lib
RNDU = m.RNDU


def main():
    per_node = {}
    for path in sorted(R.glob("2229_q_mpfr_node*.json")):
        data = json.loads(path.read_text(encoding="utf-8"))
        if data.get("status") != "MPFR-Q-INTERVAL-NODE-OUTWARD":
            continue
        ni = int(data["scope"]["node_index"])
        acc = m.M()
        tmp = m.M()
        try:
            lib.mpfr_set_d(C.byref(acc.x), C.c_double(0.0), 0)
            n_rows = 0
            for row in data["rows"]:
                for value in (row["gl"], row["simpson"]):
                    lib.mpfr_set_d(C.byref(tmp.x), C.c_double(value), 0)
                    lib.mpfr_add(C.byref(acc.x), C.byref(acc.x),
                                 C.byref(tmp.x), RNDU)
                n_rows += 1
            recomputed = acc.get_d(RNDU)
        finally:
            acc.clear()
            tmp.clear()
        reported = data["exp_lipschitz_charge"]
        per_node[str(ni)] = {
            "rows": n_rows,
            "recomputed_mpfr_rndu": recomputed,
            "reported_2229": reported,
            "reported_minus_recomputed": reported - recomputed,
            "relative_slack": (reported - recomputed) / recomputed,
        }
    deficits = {k: v["reported_minus_recomputed"] for k, v in per_node.items()
                if v["reported_minus_recomputed"] < 0}
    charges = {k: v["recomputed_mpfr_rndu"] for k, v in per_node.items()}
    worst = max(charges, key=lambda k: charges[k])
    result = {
        "record": 2232,
        "status": ("FAMILY-STITCH-CLOSED" if not deficits and len(per_node) == 30
                   else "FAMILY-STITCH-REVIEW"),
        "scope": {"nodes": len(per_node), "rows_per_node": 30,
                  "source": "results/2229_q_mpfr_node*.json"},
        "lemma": {
            "statement": "nextafter-up(fl(fl(T+g)+s)) >= T+g+s for g,s >= 0 "
                         "with g,s outward-rounded binary64",
            "mechanism": "two round-to-nearest steps lose at most one spacing; "
                         "one nextafter step upward adds one spacing",
            "status": "paper lemma, verified numerically here against the "
                      "committed rows",
        },
        "per_node": per_node,
        "deficits": deficits,
        "worst_node": int(worst),
        "max_charge_mpfr": charges[worst],
        "min_charge_mpfr": min(charges.values()),
        "max_relative_slack": max(v["relative_slack"] for v in per_node.values()),
        "min_relative_slack": min(v["relative_slack"] for v in per_node.values()),
        "nonclaims": [
            "binary64 operands are taken as exact (discrete-defined "
            "convention; record 2230)",
            "the paper lemma is not yet formalized in Lean",
            "no producer or RH claim",
        ],
        "provenance": {
            "script": "scripts/routea_weighted_zero_family_stitch_2232.py",
            "mpfr_backend": "routea_weighted_zero_mpfr_exp_binding_2223.py",
        },
    }
    out = R / "2232_family_stitch_closure.json"
    out.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k: result[k] for k in
                      ("status", "worst_node", "max_charge_mpfr",
                       "min_charge_mpfr", "deficits",
                       "max_relative_slack", "min_relative_slack")},
                     indent=2), flush=True)


if __name__ == "__main__":
    main()