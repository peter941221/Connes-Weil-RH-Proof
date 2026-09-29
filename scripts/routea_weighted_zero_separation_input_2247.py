#!/usr/bin/env python3
"""2247 - Measured separation input for the 2157 near-pin derivative floor.

At the three 2103 stress candidates, assemble the exact owner node set used
by the known-prefix construction (the 1994 orbit/real targets plus the
in-ball critical-line zeros), classify nodes into nonzero targets and source
zeros, and measure every target-to-source-zero separation.  The 2157 floor

    derivativeCost >= 4 exp(-X S) / (delta X L^2)

(X = half-support, L = support width, S = max real part over the segment,
delta = target-to-pin distance) is then evaluated at the measured minimum,
so the floor is finite and explicit at each candidate.

Writes results/2247_separation_input.json.  Screening artifact only.
"""

import json
import math
import sys
from pathlib import Path

import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import fourpoint_owner_completion_1980 as r80  # noqa: E402
import routea_opposite_gates_height_1994 as r94  # noqa: E402

RECORD = 2247
DELTA = 0.445
N_SHELL = 0
G13 = 48.005150881167159
GAMMAS = ((r94.G7 + r94.G8) / 2.0,
          (r94.G8 + 43.327073280914999) / 2.0,
          (43.327073280914999 + G13) / 2.0)
ANCHOR_2103 = "results/2103_full_known_prefix_direct_owner_grid_m6400.json"
OUTPUT = ROOT / "results" / "2247_separation_input.json"


def assemble_owner(gamma):
    """The 2103 node assembly: fixed 1994 nodes plus in-ball zeros."""
    rho = (0.5 + DELTA) + 1j * gamma
    nodes, values = r94.owner_nodes_ext(rho, gamma)
    nodes = [complex(z) for z in nodes]
    values = [complex(v) for v in values]
    radius = r80.ball_radius(rho, N_SHELL)
    mp.mp.dps = 50
    added = []
    for index in range(1, 31):
        height = float(mp.im(mp.zetazero(index)))
        z = 0.5 + 1j * height
        if abs(z - rho) <= radius and all(abs(z - e) > 1e-6 for e in nodes):
            nodes.append(z)
            values.append(0j)
            added.append(height)
    return rho, radius, nodes, values, added


def floor_2157(delta_sep, support, s_real):
    X = support / 2.0
    L = support
    return 4.0 * math.exp(-X * s_real) / (delta_sep * X * L * L)


def candidate_row(gamma, support):
    rho, radius, nodes, values, added = assemble_owner(gamma)
    targets = [(z, v) for z, v in zip(nodes, values) if v != 0]
    pins = []
    for z, v in zip(nodes, values):
        if v != 0:
            continue
        entry = {"node": [z.real, z.imag]}
        if abs(z.imag) <= 1e-9:
            entry["kind"] = "real_axis_pin"
        elif abs(z.real - 0.5) > 1e-9:
            entry["kind"] = "off_line_pin"
        else:
            zval = float(abs(mp.siegelz(mp.mpf(z.imag))))
            entry["abs_Z"] = zval
            entry["kind"] = ("critical_line_zero" if zval < 1e-9
                             else "critical_line_nonzero_pin")
        pins.append((z, entry))
    per_target = []
    worst = None
    for t, v in targets:
        best = None
        for z, entry in pins:
            d = abs(t - z)
            if best is None or d < best[0]:
                best = (d, z, entry)
        s_real = max(abs(t.real), abs(best[1].real))
        per_target.append({
            "target": [t.real, t.imag],
            "value": [v.real, v.imag],
            "min_separation": best[0],
            "nearest_pin": [best[1].real, best[1].imag],
            "nearest_pin_kind": best[2]["kind"],
            "floor_2157_at_min_separation": floor_2157(best[0], support,
                                                       s_real),
        })
        if worst is None or best[0] < worst[0]:
            worst = (best[0], t, best[1], best[2])
    target_distances = []
    for i, (t1, _) in enumerate(targets):
        for t2, _ in targets[i + 1:]:
            target_distances.append({
                "pair": [[t1.real, t1.imag], [t2.real, t2.imag]],
                "distance": abs(t1 - t2),
            })
    kinds = {}
    for _, entry in pins:
        kinds[entry["kind"]] = kinds.get(entry["kind"], 0) + 1
    s_worst = max(abs(worst[1].real), abs(worst[2].real))
    return {
        "gamma": gamma,
        "rho": [rho.real, rho.imag],
        "radius": radius,
        "support": support,
        "n_nodes": len(nodes),
        "n_targets_nonzero": len(targets),
        "n_pins": len(pins),
        "pin_kinds": kinds,
        "n_in_ball_added": len(added),
        "per_target": per_target,
        "min_separation": worst[0],
        "min_separation_pair": {
            "target": [worst[1].real, worst[1].imag],
            "pin": [worst[2].real, worst[2].imag],
            "pin_kind": worst[3]["kind"],
        },
        "floor_2157_at_min_separation": floor_2157(worst[0], support,
                                                   s_worst),
        "target_to_target": target_distances,
        "detector_automatic_separation": DELTA,
    }


def main():
    anchored = json.loads((ROOT / ANCHOR_2103).read_text(encoding="utf-8"))
    rows = []
    for gamma in GAMMAS:
        anchor_rows = [r for r in anchored["rows"]
                       if r["gamma"] == gamma and r["delta"] == DELTA]
        assert anchor_rows, f"no 2103 anchor row for gamma={gamma}"
        support = anchor_rows[0]["support"]
        rows.append(candidate_row(gamma, support))
    overall = min(rows, key=lambda r: r["min_separation"])
    result = {
        "record": RECORD,
        "status": "SEPARATION-INPUT-MEASURED",
        "date": "2026-09-30",
        "proposition": (
            "At a fixed candidate (rho, N): every nonzero target of the "
            "owner (the 1994 orbit/real targets with value +-1) is separated "
            "from every zero-valued interpolation pin that is not itself a "
            "target, with |t - z| >= s_min, and the 2157 derivative floor "
            "4 exp(-X S)/(delta X L^2) with delta = s_min is finite and "
            "explicit.  Uniformity in the configuration requires a certified "
            "zero-isolation procedure for every rho; per fixed rho it is a "
            "finite certified check."),
        "measured": {
            "worst_candidate_gamma": overall["gamma"],
            "min_separation": overall["min_separation"],
            "min_separation_pair": overall["min_separation_pair"],
            "floor_2157_at_min_separation":
                overall["floor_2157_at_min_separation"],
        },
        "target_classification": (
            "nonzero targets: rho (value 1), 1 - conj(rho) (value -1), "
            "rho + 1/2 (value -1); zero-valued pins: conj(rho), 1 - rho "
            "(off-line), the real-axis points 0.5/1/1.5, and the kill "
            "ordinates plus the in-ball zeros added by the 2103 loop.  The "
            "1994 kill list carries one non-zero pinned ordinate: "
            "27.67032193035704 is not a zeta zero (|zeta| = 2.845101349, "
            "no Hardy-Z sign change; audit in results/2245).  Pins are "
            "labelled by kind in each row."),
        "alternatives_2157": [
            "explicit separation bound (this record, measured at the three "
            "candidates; the formal uniform version needs certified zero "
            "isolation)",
            "cost estimate using the full node geometry (the direct solver "
            "actually does this; the 2109/2103 ledgers price the "
            "construction without charging a derivative seminorm)",
            "signed argument avoiding the derivative seminorm charge",
        ],
        "rows": rows,
        "nonclaims": [
            "measured separations at three candidates are not a uniform "
            "separation theorem over all rho",
            "no producer GO, no RH claim",
        ],
        "provenance": {
            "script": "scripts/routea_weighted_zero_separation_input_2247.py",
            "anchor_2103": ANCHOR_2103,
        },
    }
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n",
                      encoding="utf-8", newline="\n")
    print(json.dumps({"status": result["status"],
                      "measured": result["measured"]}, indent=2))


if __name__ == "__main__":
    main()