"""Reprice the sigma=+1/2 cell2700 three-piece summand at the correction pair.

Companion of price_cell2700_minus_correction_2569.py for the plus sign
(record 2571). The committed sigma = +1/2 cell2700 certificate (2563) rests
on the coarse 2551 boundary envelope; this pilot evaluates the FINE
three-piece structure externally at the base pair (selfcheck against the
committed plus aggregates: the 2558 stage-A midpoint/third/curvature chain,
the 2556 shared endpoint uppers, the 2563 first-jet and coarse bound) and
then reprices the same structure at the ideal_correction_coefficient pair
with the 1e-28 per-family charge. No Lean claim; the repriced bound is the
pilot cross-check for the 2571 stage-B regeneration.
"""
from fractions import Fraction as Q
from math import ceil, hypot, isqrt
import hashlib
import json
from typing import Any

from generate_complex_exp_node_2541 import ROOT, CAPTURE, add, mul, up
from price_boundary_precision_2547 import precision_evaluate
from price_cell2700_minus_2565 import scalar_defs
from routea_derivative_pricing_2543 import multiplier
from routea_exp_schedule_probe_2542 import R, STEP

RECORD = 2571
CHARGE_BASE = Q(1, 10 ** 30)
CHARGE_CORRECTION = Q(1, 10 ** 28)
BITS = 160

COMMITTED_BASE = dict(
    mid_upper=Q(8777, 50000000),
    jet1_upper=Q(147, 50000000),
    n0l_upper=Q(179, 2000000000),
    n0r_upper=Q(873, 10000000000),
    third_upper=Q(4373, 500000),
    curvature_upper=Q(91, 500000),
    coarse_cell_bound=Q(236901, 10 ** 12),
    coarse_piece_sum_display=2.369005939687927e-7,
)


def families():
    raw = json.loads(CAPTURE.read_text())["owner_capture"]["families_hex"]
    out = []
    for values in raw:
        width, theta = (Q.from_float(float.fromhex(v)) for v in values)
        out.append((width * width, theta))
    return out


def coefficient_centers(mode):
    rows = json.loads(
        (ROOT / "results/2338_exact_interpolation_repair.json").read_text())["coefficient_rows"]
    key = "ideal_base_coefficient" if mode == "base" else "ideal_correction_coefficient"
    out = []
    for row in rows:
        box = row[key]
        out.append(tuple((Q(box[p]["lower_exact"]) + Q(box[p]["upper_exact"])) / 2
                         for p in ("real", "imag")))
    return out


def unit_jet(family, order, sigma, x):
    radius, theta = family
    center, error, _ = precision_evaluate(radius, theta, x, sigma, BITS)
    if center == (Q(0), Q(0)):
        return (Q(0), Q(0)), Q(0)
    factor = (Q(1), Q(0)) if order == 0 else multiplier(order, radius, theta, sigma, x)
    return mul(factor, center), up(sum(abs(v) for v in factor) * error + Q(1, 2 ** 99))


def norm_ceiling(total, scale):
    square = total[0] * total[0] + total[1] * total[1]
    return Q(isqrt(square.numerator * scale * scale // square.denominator) + 1, scale)


def magnitude(total):
    return hypot(float(total[0]), float(total[1]))


def signed_aggregate(centers, jets, scale):
    """Upper for |sum c_i * u_i| plus the rationalization charge sum."""
    total, charge = (Q(0), Q(0)), Q(0)
    for c, (value, radius) in zip(centers, jets):
        total = add(total, mul(c, value))
        charge += sum(abs(v) for v in c) * radius
    upper = norm_ceiling(total, scale) + Q(1, scale) + charge
    return upper, charge, total


def third_envelopes():
    left_src = (ROOT / "ConnesWeilRH/Dev/C1RouteABatchC02700PlusLeftBounds2558.lean").read_text()
    right_src = (ROOT / "ConnesWeilRH/Dev/C1RouteABatchC02700PlusRightBounds2558.lean").read_text()
    fourth_src = (ROOT / "ConnesWeilRH/Dev/C1RouteABatchC02700PlusFourth2558.lean").read_text()
    vals = {}
    vals.update(scalar_defs(left_src, r"batchC02700PlusLeftP\d{3}NormUpper2558"))
    vals.update(scalar_defs(right_src, r"batchC02700PlusRightP\d{3}NormUpper2558"))
    vals.update(scalar_defs(fourth_src, r"batchC02700PlusFourthP\d{3}Upper2558"))
    assert len(vals) == 90, len(vals)
    out = []
    for i in range(30):
        out.append(max(vals[f"batchC02700PlusLeftP{i:03d}NormUpper2558"],
                       vals[f"batchC02700PlusRightP{i:03d}NormUpper2558"])
                   + vals[f"batchC02700PlusFourthP{i:03d}Upper2558"] * HALF)
    return out


def third_aggregate(centers, charge, envelopes):
    return sum((sum(abs(v) for v in c) + charge) * t for c, t in zip(centers, envelopes))


def repriced_bound(mode: str) -> tuple[dict[str, Any], dict[str, Any]]:
    sigma = Q(1, 2)
    charge = CHARGE_BASE if mode == "base" else CHARGE_CORRECTION
    centers = coefficient_centers(mode)
    j1, j1_charge, j1_total = signed_aggregate(
        centers, [unit_jet(f, 1, sigma, MID) for f in FAMILIES], 10 ** 8)
    mid, mid_charge, mid_total = signed_aggregate(
        centers, [unit_jet(f, 2, sigma, MID) for f in FAMILIES], 10 ** 8)
    n0l, n0l_charge, n0l_total = signed_aggregate(
        centers, [unit_jet(f, 0, sigma, LEFT) for f in FAMILIES], 10 ** 10)
    n0r, n0r_charge, n0r_total = signed_aggregate(
        centers, [unit_jet(f, 0, sigma, RIGHT) for f in FAMILIES], 10 ** 10)
    agg = third_aggregate(centers, charge, ENVELOPES)
    curvature = mid + agg * HALF
    pieces = (STEP_FULL * curvature,
              2 * abs(sigma) * STEP_FULL * (j1 + curvature * HALF),
              sigma ** 2 * (HALF * (n0l + n0r) + curvature * (STEP_FULL ** 3 / 12)))
    total = sum(pieces)
    scale = 10 ** 12
    bound = Q(ceil(total * scale), scale)
    exact = dict(charge=charge, j1_upper=j1, j1_charge=j1_charge,
                 mid_upper=mid, mid_charge=mid_charge,
                 n0l_upper=n0l, n0l_charge=n0l_charge,
                 n0r_upper=n0r, n0r_charge=n0r_charge,
                 third_aggregate_l1=agg, curvature_upper=curvature,
                 cell_bound=bound)
    display = dict(mode=mode, j1_total=magnitude(j1_total), mid_total=magnitude(mid_total),
                   n0l_total=magnitude(n0l_total), n0r_total=magnitude(n0r_total),
                   third_aggregate=float(agg), curvature=float(curvature),
                   pieces=[float(v) for v in pieces], piece_sum=float(total),
                   headroom=float(bound / total))
    return exact, display


FAMILIES = families()
LEFT = -R + 2700 * STEP
RIGHT = -R + 2701 * STEP
MID = -R + Q(5401, 2) * STEP
STEP_FULL = 2 * R / 10240
HALF = STEP_FULL / 2
assert LEFT == Q(-7929856121, 2560000000)
assert RIGHT == Q(-158531586419, 51200000000)
ENVELOPES = third_envelopes()


def stringify(exact):
    return {key: (str(value) if isinstance(value, Q) else value)
            for key, value in exact.items()}


def enclosure_2561_cell2700():
    """2561-style whole-cell enclosure of the same integrand at cell2700, sigma=+1/2."""
    from flint import acb, arb, ctx
    import price_correction_second_2561 as p2561
    import routea_owner_whole_cell_2535 as wbase
    ctx.prec = 192
    sigma = Q(1, 2)
    fams = p2561.load_families()
    step = 2 * wbase.RADIUS / 10240
    h = wbase.lift(step)
    a = -wbase.RADIUS + 2700 * step
    b = a + step
    left, thirds_l = p2561.point(fams, a, sigma)
    right, thirds_r = p2561.point(fams, b, sigma)
    center, error, third = acb(0), arb(0), arb(0)
    for f, l, r in zip(fams, thirds_l, thirds_r):
        j2 = p2561.jets(f, (a + b) / 2, sigma, 2)[2]
        center += f["center"] * j2
        error += f["error"] * abs(j2)
        third += f["scale"] * (max(l, r) + h / 2 * p2561.envelope(f, a, b, sigma))
    curvature = wbase.upper(abs(center) + error + h / 2 * third)
    node = wbase.exact_upper(h / 2 * (left + right))
    remainder = wbase.exact_upper(h ** 3 / 12 * curvature)
    return dict(node=float(node), remainder=float(remainder),
                total=float(node + remainder))


def main():
    base_exact, base_display = repriced_bound("base")
    # the fine chain must sit under every committed plus-side aggregate at
    # this cell: the stage-A midpoint/third/curvature bounds, the 2556 shared
    # endpoint uppers, the 2563 first-jet bound, and the coarse 2563 total.
    checks = dict(
        mid_vs_committed=float(base_exact["mid_upper"] - COMMITTED_BASE["mid_upper"]),
        j1_vs_committed=float(base_exact["j1_upper"] - COMMITTED_BASE["jet1_upper"]),
        n0l_vs_committed=float(base_exact["n0l_upper"] - COMMITTED_BASE["n0l_upper"]),
        n0r_vs_committed=float(base_exact["n0r_upper"] - COMMITTED_BASE["n0r_upper"]))
    assert all(abs(v) <= 3 * 10 ** -6 for v in checks.values()), checks
    assert base_exact["mid_upper"] <= COMMITTED_BASE["mid_upper"]
    assert base_exact["j1_upper"] <= COMMITTED_BASE["jet1_upper"]
    # the third aggregate has no exact committed scalar (the module scalar
    # 4373/500000 carries thirty per-family round-ups over the exact sum), so
    # it is checked by dominance, not by a tight tolerance.
    assert base_exact["third_aggregate_l1"] <= COMMITTED_BASE["third_upper"]
    # the fine curvature chain must reproduce the committed coarse envelope:
    # mid + agg*h/2 <= 91/500000 is exactly the 2551-value theorem the
    # stage-A Integral module certifies (batchC02700PlusCellCurvatureBound2558).
    assert base_exact["curvature_upper"] <= COMMITTED_BASE["curvature_upper"]
    assert base_display["piece_sum"] <= float(COMMITTED_BASE["coarse_cell_bound"]), \
        base_display["piece_sum"]
    corr_exact, corr_display = repriced_bound("correction")
    cross = enclosure_2561_cell2700()
    pin = Q("666472.585392")
    result = dict(
        record=RECORD,
        scope=("sigma=+1/2 cell2700 fine three-piece repricing at the ideal_correction_coefficient "
               "pair; external exact arithmetic; no Lean claim"),
        base_selfcheck=dict(repriced=stringify(base_exact), displays=base_display,
                            committed_deltas=checks,
                            coarse_2563_piece_sum=COMMITTED_BASE["coarse_piece_sum_display"],
                            verdict="PIPELINE_UNDER_COMMITTED_PLUS_AGGREGATES"),
        correction_repricing=dict(exact=stringify(corr_exact), displays=corr_display),
        cross_check_2561_cell2700=dict(
            enclosure=cross,
            three_piece_vs_enclosure=corr_display["piece_sum"] / cross["total"],
            note=("2561 trapezoid enclosure of exp(sigma*x)f'' over the same cell; both "
                  "bound the same integral, so they must agree in scale, not bitwise")),
        correction_pin=str(pin),
        three_piece_grid_extrapolation=corr_display["piece_sum"] * 10240,
        extrapolation_caveat=("cell2700 only; the node-dominated profile is not uniform "
                              "across the grid, so this extrapolation is an upper-bound sanity "
                              "figure, not a budget claim"),
        rh_claim=False, lean_certificate=False,
        source_sha256={name: hashlib.sha256(
            (ROOT / name).read_bytes()).hexdigest() for name in (
            "scripts/price_cell2700_plus_correction_2571.py",
            "ConnesWeilRH/Dev/C1RouteABatchC02700PlusLeftBounds2558.lean",
            "ConnesWeilRH/Dev/C1RouteABatchC02700PlusRightBounds2558.lean",
            "ConnesWeilRH/Dev/C1RouteABatchC02700PlusFourth2558.lean")})
    (ROOT / f"results/{RECORD}_cell2700_plus_correction_repricing.json").write_text(
        json.dumps(result, indent=2) + "\n")
    print("BASE_SELFCHECK", json.dumps(checks), flush=True)
    print("BASE_PIECES", [float(f"{v:.6e}") for v in base_display["pieces"]],
          "sum", float(f"{base_display['piece_sum']:.10e}"),
          "coarse_2563_bound", COMMITTED_BASE["coarse_cell_bound"], flush=True)
    print("CORRECTION_PIECES", [float(f"{v:.6e}") for v in corr_display["pieces"]],
          "sum", float(f"{corr_display['piece_sum']:.10e}"),
          "bound", corr_exact["cell_bound"], flush=True)
    print("CORRECTION_TOTALS", json.dumps(
        {k: float(f"{v:.10e}") for k, v in corr_display.items()
         if k in ("j1_total", "mid_total", "n0l_total", "n0r_total",
                  "third_aggregate", "curvature")}), flush=True)
    print("CROSS_CHECK_2561_CELL2700", json.dumps(cross),
          "ratio three-piece/enclosure",
          float(f"{corr_display['piece_sum'] / cross['total']:.6f}"), flush=True)


if __name__ == "__main__":
    main()
