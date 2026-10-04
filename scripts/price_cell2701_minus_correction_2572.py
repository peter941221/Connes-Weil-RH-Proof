"""Reprice the sigma=-1/2 cell2701 three-piece summand at the correction pair.

Companion of price_cell2700_minus_correction_2569.py at the adjacent cell
2701 (record 2572). The committed 2558 chain covers cell 2701 at the base
pair only; this pilot re-evaluates the same three-piece structure in exact
external arithmetic at the correction pair (1e-28 per-family charge) and
validates the recomputation pipeline against the committed base-pair
scalars of the 2701 chain (curvature 3877/1000000, integral
2433/1000000000000, right endpoint 117/62500000). No Lean claim; the
repriced bound is the pilot cross-check for the 2572 stage generation.
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

RECORD = 2572
CHARGE_BASE = Q(1, 10 ** 30)
CHARGE_CORRECTION = Q(1, 10 ** 28)
BITS = 160

COMMITTED_BASE = dict(
    mid_upper=Q(187703, 50000000),
    right_upper=Q(117, 62500000),
    third_aggregate=Q(38347, 200000),
    # the 2558 Integral module at cell 2701 is the per-family charge table
    # (fourth-remainder class), NOT a three-piece cell total -- informational
    integral_module_bound=Q(2433, 10 ** 12),
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
    left_src = (ROOT / "ConnesWeilRH/Dev/C1RouteABatchC02701MinusLeftBounds2558.lean").read_text()
    right_src = (ROOT / "ConnesWeilRH/Dev/C1RouteABatchC02701MinusRightBounds2558.lean").read_text()
    fourth_src = (ROOT / "ConnesWeilRH/Dev/C1RouteABatchC02701MinusFourth2558.lean").read_text()
    vals = {}
    vals.update(scalar_defs(left_src, r"batchC02701MinusLeftP\d{3}NormUpper2558"))
    vals.update(scalar_defs(right_src, r"batchC02701MinusRightP\d{3}NormUpper2558"))
    vals.update(scalar_defs(fourth_src, r"batchC02701MinusFourthP\d{3}Upper2558"))
    assert len(vals) == 90, len(vals)
    out = []
    for i in range(30):
        out.append(max(vals[f"batchC02701MinusLeftP{i:03d}NormUpper2558"],
                       vals[f"batchC02701MinusRightP{i:03d}NormUpper2558"])
                   + vals[f"batchC02701MinusFourthP{i:03d}Upper2558"] * HALF)
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
LEFT = -R + 2701 * STEP
RIGHT = -R + 2702 * STEP
MID = -R + Q(5403, 2) * STEP
STEP_FULL = 2 * R / 10240
HALF = STEP_FULL / 2
assert LEFT == -R + Q(2701) * STEP_FULL
assert RIGHT == -R + Q(2702) * STEP_FULL
ENVELOPES = third_envelopes()


def stringify(exact):
    return {key: (str(value) if isinstance(value, Q) else value)
            for key, value in exact.items()}


def main():
    base_exact, base_display = repriced_bound("base")
    # the fine pipeline must sit against the committed cell-2701 base
    # scalars: midpoint/endpoint are same-quantity scalars (tight |Delta|,
    # the endpoint carries a +1.4e-16 rounding-order artifact because the
    # committed render folds the evaluation charge before its decimal
    # ceiling while this pipeline adds it after); the committed coarse
    # third aggregate is thirty per-family round-ups, so dominance only
    checks = dict(
        mid_vs_committed=float(base_exact["mid_upper"] - COMMITTED_BASE["mid_upper"]),
        n0r_vs_committed=float(base_exact["n0r_upper"] - COMMITTED_BASE["right_upper"]))
    assert abs(checks["mid_vs_committed"]) <= 3 * 10 ** -6, checks
    assert abs(checks["n0r_vs_committed"]) <= 10 ** -15, checks
    assert base_exact["mid_upper"] <= COMMITTED_BASE["mid_upper"]
    assert base_exact["third_aggregate_l1"] <= COMMITTED_BASE["third_aggregate"]
    assert base_exact["curvature_upper"] <= (COMMITTED_BASE["mid_upper"]
                                             + COMMITTED_BASE["third_aggregate"] * HALF)
    corr_exact, corr_display = repriced_bound("correction")
    result = dict(
        record=RECORD,
        scope=("sigma=-1/2 cell2701 three-piece repricing at the ideal_correction_coefficient "
               "pair; external exact arithmetic; no Lean claim"),
        base_selfcheck=dict(repriced=stringify(base_exact), displays=base_display,
                            committed_deltas=checks,
                            committed=dict((k, str(v)) for k, v in COMMITTED_BASE.items()),
                            verdict="PIPELINE_UNDER_COMMITTED_CELL2701_SCALARS"),
        correction_repricing=dict(exact=stringify(corr_exact), displays=corr_display),
        rh_claim=False, lean_certificate=False,
        source_sha256={name: hashlib.sha256(
            (ROOT / name).read_bytes()).hexdigest() for name in (
            "scripts/price_cell2701_minus_correction_2572.py",
            "ConnesWeilRH/Dev/C1RouteABatchC02701MinusLeftBounds2558.lean",
            "ConnesWeilRH/Dev/C1RouteABatchC02701MinusRightBounds2558.lean",
            "ConnesWeilRH/Dev/C1RouteABatchC02701MinusFourth2558.lean")})
    (ROOT / f"results/{RECORD}_cell2701_minus_correction_repricing.json").write_text(
        json.dumps(result, indent=2) + "\n")
    print("BASE_SELFCHECK", json.dumps(checks), flush=True)
    print("BASE_PIECES", [float(f"{v:.6e}") for v in base_display["pieces"]],
          "sum", float(f"{base_display['piece_sum']:.10e}"), flush=True)
    print("CORRECTION_PIECES", [float(f"{v:.6e}") for v in corr_display["pieces"]],
          "sum", float(f"{corr_display['piece_sum']:.10e}"),
          "bound", corr_exact["cell_bound"], flush=True)
    print("CORRECTION_TOTALS", json.dumps(
        {k: float(f"{v:.10e}") for k, v in corr_display.items()
         if k in ("j1_total", "mid_total", "n0l_total", "n0r_total",
                  "third_aggregate", "curvature")}), flush=True)


if __name__ == "__main__":
    main()
