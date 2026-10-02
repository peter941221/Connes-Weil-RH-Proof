"""2455: quadrature-import pricing screen (diagnostic only).

Reads the certified 2342 endpoint artifact (exact rational intervals,
120001-node grid) and answers the coarsening question for the planned
Lean quadrature import: how far can the uniform grid be coarsened before
the one-sided trapezoid panel term pushes the min-product through the
frozen pin?  Panel terms scale as h^2, so the screen recomputes the
min-product as a function of the coarsening factor f = (N-1)/(N'-1):

  min((B2p + B2a f^2)(C0p + C0a f^2), (C2p + C2a f^2)(B0p + B0a f^2))

with per-channel point/panel endpoint maxima lifted exactly from the
artifact.  No new numerics, no capture data, no producer.  Verdict is a
go/no-go for grid coarsening and a node-count floor; it is not a
certificate and imports nothing into Lean.
"""
import json
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "results/2342_direct_ideal_strip.json"
OUT = ROOT / "results/2455_quadrature_import_screen.json"

PIN = Fraction(5289085703, 2000)
N_FULL = 120001


def main():
    art = json.loads(SRC.read_text())
    pt, pa = {}, {}
    for ep in art["endpoints"]:
        sigma = ep["sigma_exact"]
        for channel in ("base", "correction"):
            c = ep["channels"][channel]
            for key, tag in (("m0", "S0"), ("d2", "S2")):
                pt[(channel, tag, sigma)] = Fraction(
                    c[f"{key}_point_upper"]["upper_exact"])
                pa[(channel, tag, sigma)] = Fraction(
                    c[f"{key}_panel_upper"]["upper_exact"])

    def epmax(channel, tag, kind):
        return max(kind[(channel, tag, s)] for s in ("-1/2", "1/2"))

    bounds = {}
    for channel in ("base", "correction"):
        for tag in ("S0", "S2"):
            bounds[f"{channel}_{tag}_point"] = str(epmax(channel, tag, pt))
            bounds[f"{channel}_{tag}_panel"] = str(epmax(channel, tag, pa))

    B0p, B0a = epmax("base", "S0", pt), epmax("base", "S0", pa)
    C0p, C0a = epmax("correction", "S0", pt), epmax("correction", "S0", pa)
    B2p, B2a = epmax("base", "S2", pt), epmax("base", "S2", pa)
    C2p, C2a = epmax("correction", "S2", pt), epmax("correction", "S2", pa)

    def prod(f):
        return min((B2p + B2a * f * f) * (C0p + C0a * f * f),
                   (C2p + C2a * f * f) * (B0p + B0a * f * f))

    full = prod(Fraction(1))
    published = Fraction(
        art["continuum_min_product_upper_exact"])
    # The published product upper is built from dyadic-rounded exported
    # endpoints, so exact fraction equality with a recomputation from the
    # raw m0/d2 endpoint intervals is not expected; require agreement to
    # a relative 1e-12 instead.
    cross_ok = abs(full - published) <= published / Fraction(10 ** 12)

    lo, hi = Fraction(1), Fraction(200000)
    for _ in range(200):
        mid = (lo + hi) / 2
        if prod(mid) <= PIN:
            lo = mid
        else:
            hi = mid
    n_floor = float(Fraction(N_FULL - 1) / lo) + 1

    table = []
    for n in (60001, 80001, 100001, 110001, 120001):
        f = Fraction(N_FULL - 1, n - 1)
        table.append({
            "nodes": n,
            "min_product": str(prod(f)),
            "ratio_to_pin": float(prod(f) / PIN),
        })

    screen = {
        "record": 2455,
        "verdict": "QUADRATURE-SCREEN-COMPLETE" if cross_ok
        else "QUADRATURE-SCREEN-CROSS-CHECK-FAIL",
        "scope": ("coarsening pricing of the 2342 certified endpoint "
                  "intervals for the planned Lean quadrature import; "
                  "diagnostic only, no Lean import, no producer GO, "
                  "no RH claim"),
        "source_artifact_sha256": __import__("hashlib").sha256(
            SRC.read_bytes()).hexdigest(),
        "nodes_full": N_FULL,
        "min_product_full": str(full),
        "cross_check_matches_published": cross_ok,
        "frozen_pin": str(PIN),
        "slack_pin_over_full": float(PIN / full),
        "panel_share_base_S0": float(B0a / (B0p + B0a)),
        "panel_share_correction_S2": float(C2a / (C2p + C2a)),
        "max_h_coarsening": float(lo),
        "node_count_floor": round(n_floor),
        "coarsening_table": table,
        "lean_import_go": False,
        "rh_claim": False,
    }
    OUT.write_text(json.dumps(screen, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "verdict": screen["verdict"],
        "cross_check": cross_ok,
        "slack": screen["slack_pin_over_full"],
        "panel_share_C2": screen["panel_share_correction_S2"],
        "node_floor": screen["node_count_floor"],
    }, indent=2))


if __name__ == "__main__":
    main()
