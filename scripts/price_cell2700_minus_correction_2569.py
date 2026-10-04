"""Reprice the sigma=-1/2 cell2700 three-piece summand at the correction pair.

Record 2568 found the committed cell2700 correction-second certificates (2563,
2565) and their 2558/2556 aggregate layers instantiated at the record-2338
ideal_base_coefficient rows, while the 2560 two-channel consumer needs the
ideal_correction_coefficient rows. This pilot re-evaluates the SAME three-piece
certificate structure in exact external arithmetic at the correction pair
(correction midpoints, 1e-28 per-family charge) and validates the recomputation
pipeline by first reproducing the committed base-pair aggregates of the 2565
pricing. No Lean claim; the repriced bound informs the 2569 regeneration.
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

RECORD = 2569
CHARGE_BASE = Q(1, 10 ** 30)
CHARGE_CORRECTION = Q(1, 10 ** 28)
BITS = 160

COMMITTED_BASE = dict(
    mid_upper=Q(377443, 10 ** 8),
    jet1_upper=Q(1283, 20000000),
    n0l_upper=Q(19793, 10 ** 10),
    n0r_upper=Q(9637, 5 * 10 ** 9),
    cell_bound=Q(5071985, 10 ** 12),
    third_l1_literal=(
        Q(90003427712263015194132112776719368699858940112810875667767574999223, 1) * 10 ** 109
        + Q(59182773713947293363288007825817794791100237735426283343558342716365, 1) * 10 ** 41
        + Q(82011618282523054589118517575045863528287, 1)) / (
        Q(47634102635436893179040485073748265163400240214004076398607741693502, 1) * 10 ** 110
        + Q(37638579964630310525669957720903259013261598826023705212365233289009, 1) * 10 ** 42
        + Q(561600000000000000000000000000000000000000, 1)),
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
    left_src = (ROOT / "ConnesWeilRH/Dev/C1RouteABatchC02700MinusLeftBounds2558.lean").read_text()
    right_src = (ROOT / "ConnesWeilRH/Dev/C1RouteABatchC02700MinusRightBounds2558.lean").read_text()
    fourth_src = (ROOT / "ConnesWeilRH/Dev/C1RouteABatchC02700MinusFourth2558.lean").read_text()
    vals = {}
    vals.update(scalar_defs(left_src, r"batchC02700MinusLeftP\d{3}NormUpper2558"))
    vals.update(scalar_defs(right_src, r"batchC02700MinusRightP\d{3}NormUpper2558"))
    vals.update(scalar_defs(fourth_src, r"batchC02700MinusFourthP\d{3}Upper2558"))
    assert len(vals) == 90, len(vals)
    out = []
    for i in range(30):
        out.append(max(vals[f"batchC02700MinusLeftP{i:03d}NormUpper2558"],
                       vals[f"batchC02700MinusRightP{i:03d}NormUpper2558"])
                   + vals[f"batchC02700MinusFourthP{i:03d}Upper2558"] * HALF)
    return out


def third_aggregate(centers, charge, envelopes):
    return sum((sum(abs(v) for v in c) + charge) * t for c, t in zip(centers, envelopes))


def repriced_bound(mode: str) -> tuple[dict[str, Any], dict[str, Any]]:
    sigma = Q(-1, 2)
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
    """2561-style whole-cell enclosure of the same integrand at cell2700, sigma=-1/2."""
    from flint import acb, arb, ctx
    import price_correction_second_2561 as p2561
    import routea_owner_whole_cell_2535 as wbase
    ctx.prec = 192
    sigma = Q(-1, 2)
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
    committed_total = 5.071984558354379e-6
    assert base_display["piece_sum"] <= float(COMMITTED_BASE["cell_bound"]), \
        base_display["piece_sum"]
    assert abs(base_display["piece_sum"] - committed_total) <= 1e-9, \
        base_display["piece_sum"]
    assert base_exact["third_aggregate_l1"] <= COMMITTED_BASE["third_l1_literal"]
    checks = dict(
        total_vs_committed=base_display["piece_sum"] - committed_total,
        mid_vs_committed=float(base_exact["mid_upper"] - COMMITTED_BASE["mid_upper"]),
        j1_vs_committed=float(base_exact["j1_upper"] - COMMITTED_BASE["jet1_upper"]),
        n0l_vs_committed=float(base_exact["n0l_upper"] - COMMITTED_BASE["n0l_upper"]),
        n0r_vs_committed=float(base_exact["n0r_upper"] - COMMITTED_BASE["n0r_upper"]),
        third_agg_vs_literal=float(base_exact["third_aggregate_l1"]
                                   - COMMITTED_BASE["third_l1_literal"]))
    assert all(abs(v) <= 3 * 10 ** -6 for v in checks.values()), checks
    corr_exact, corr_display = repriced_bound("correction")
    cross = enclosure_2561_cell2700()
    pin = Q("666472.585392")
    result = dict(
        record=RECORD,
        scope=("sigma=-1/2 cell2700 three-piece repricing at the ideal_correction_coefficient "
               "pair; external exact arithmetic; no Lean claim"),
        base_selfcheck=dict(repriced=stringify(base_exact), displays=base_display,
                            committed_deltas=checks, cell_bound_matches_committed=True,
                            verdict="PIPELINE_REPRODUCES_COMMITTED_BASE_AGGREGATES"),
        correction_repricing=dict(exact=stringify(corr_exact), displays=corr_display),
        cross_check_2561_cell2700=dict(
            enclosure=cross,
            three_piece_vs_enclosure=corr_display["piece_sum"] / cross["total"],
            note=("2561 trapezoid enclosure of exp(sigma*x)f'' over the same cell; both "
                  "bound the same integral, so they must agree in scale, not bitwise")),
        correction_grid_average_2561=126381.73694023857 / 10240,
        correction_pin=str(pin),
        three_piece_grid_extrapolation=corr_display["piece_sum"] * 10240,
        extrapolation_caveat=("cell2700 only; the 2561 node-dominated profile is not uniform "
                              "across the grid, so this extrapolation is an upper-bound sanity "
                              "figure, not a budget claim"),
        rh_claim=False, lean_certificate=False,
        source_sha256={name: hashlib.sha256(
            (ROOT / name).read_bytes()).hexdigest() for name in (
            "scripts/price_cell2700_minus_correction_2569.py",
            "ConnesWeilRH/Dev/C1RouteABatchC02700MinusLeftBounds2558.lean",
            "ConnesWeilRH/Dev/C1RouteABatchC02700MinusRightBounds2558.lean",
            "ConnesWeilRH/Dev/C1RouteABatchC02700MinusFourth2558.lean")})
    (ROOT / f"results/{RECORD}_cell2700_minus_correction_repricing.json").write_text(
        json.dumps(result, indent=2) + "\n")
    print("BASE_SELFCHECK", json.dumps(checks), flush=True)
    print("BASE_PIECES", [float(f"{v:.6e}") for v in base_display["pieces"]],
          "bound", base_exact["cell_bound"], flush=True)
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
