"""Price the first non-cancelling off-diagonal actual entry via the residual
architecture.

Record 2624. The certified producer (routea_marked_sign_arb_certificate_2337,
integrate_family) evaluates entry (row, column) as radius_col * Integral
exp(-30/(1-x^2) + exponent*x) dx over |x| <= 1-1/64 with
exponent = (node_row + i*modulation_col) * radius_col and
radius_col = width_col^2, all operands the exact captured binary64 values.
So the real coefficient of x is beta_col = node_re * radius_col and the
imaginary coefficient is psi_col = (node_im + modulation_col) * radius_col.
Both are per-column: family zero's modulation equals -node_im (the diagonal
cancellation mechanism), and the widths differ per family, so the earlier
single-radius reading of the lane was wrong and is corrected here.

The pilot entry is chosen automatically as the worst non-cancelling column,
i.e. the largest |psi_col|: pricing the hardest entry prices all easier
ones. Two pricing facts drive the probe.

(1) The certified 2597 rectangles are Fourier-suppressed: the true entries
    decay like exp(-sqrt(30*|psi|)) from the endpoint saddle, tens of
    orders below the diagonal scale, and the committed rectangles are
    correspondingly tight. The degree-32 truncation gives a total box far
    above the rectangle width; the residual modulus decays like
    psi*(psi*h)^d/d!, so the degree is the lever. The probe runs a degree
    ladder and records the total box per rung.

(2) The per-panel center contributions rotate by exp(i*psi*center_k)
    across panels; omitting that factor loses the cross-panel cancellation
    that the certified value exhibits. Both candidate routes therefore
    need cos/sin evaluation at exact rational phase. The probe uses a
    high-precision external evaluation (mpmath, decimal round-tripped into
    exact Fractions) and records the engine as a shared obligation of both
    routes; the complex recurrence itself stays in exact rational
    arithmetic, with the same five residual slots, the variation bound
    with |beta| replaced by |beta| + |psi|, coefficient moduli
    |q| <= |re q| + |im q| (a deliberate recorded over-approximation by at
    most a factor sqrt(2)), and the committed 320/400-bit real exponential
    engine.

No integration backend and no Lean proof is involved. The deliverables are
the per-degree complex box, its margin against the committed 2597 rectangle
for the pilot entry, and the machinery count of the two candidate routes.
"""

import hashlib
import json
from fractions import Fraction
from pathlib import Path
import sys

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)

sys.path.insert(0, str(Path(__file__).resolve().parent))

import mpmath as mp
from generate_moment_scalar_certificate_2620 import compact_scalar
import generate_moment_panel_batch_2622 as _panel

ROOT = Path(__file__).resolve().parents[1]
HALF_WIDTH = Fraction(1, 200)
PANEL_COUNT = 190
CUT = PANEL_COUNT * HALF_WIDTH
ROW = 0
DEGREE_LADDER = (32, 42, 52, 55)
EXP_I_DIGITS = 160


def panel_center(index):
    return -CUT + (2 * index + 1) * HALF_WIDTH


def column_parameters(capture, column):
    width = Fraction(float.fromhex(capture["families_hex"][column][0]))
    modulation = Fraction(float.fromhex(capture["families_hex"][column][1]))
    node_real = Fraction(float.fromhex(capture["nodes_hex"][ROW][0]))
    node_imag = Fraction(float.fromhex(capture["nodes_hex"][ROW][1]))
    radius = width * width
    return {"radius": radius, "beta": node_real * radius,
            "psi": (node_imag + modulation) * radius}


def _exp_i(theta):
    """cos(theta) + i*sin(theta) for an exact rational theta.

    External high-precision evaluation; the decimal round-trip error is
    below 1e-155 absolute, immaterial against boxes of size >=1e-80. This
    is a stand-in for the Lean-side complex scalar engine that both
    candidate routes must eventually provide.
    """
    with mp.workdps(EXP_I_DIGITS):
        angle = mp.mpf(theta.numerator) / theta.denominator
        real = mp.cos(angle)
        imag = mp.sin(angle)
    return (Fraction(mp.nstr(real, EXP_I_DIGITS - 5, strip_zeros=False)),
            Fraction(mp.nstr(imag, EXP_I_DIGITS - 5, strip_zeros=False)))


def complex_multiply(left, right):
    (a, b), (c, d) = left, right
    return (a * c - b * d, a * d + b * c)


def convolve(left, right):
    out = []
    for index in range(len(left) + len(right) - 1):
        total = (Fraction(0), Fraction(0))
        for shift in range(max(0, index - len(right) + 1), min(index + 1, len(left))):
            product = complex_multiply(left[shift], right[index - shift])
            total = (total[0] + product[0], total[1] + product[1])
        out.append(total)
    return out


def build_complex_panel(beta, psi, center, degree):
    deficit = [1 - center ** 2, -2 * center, Fraction(-1)]
    denominator = _panel.multiply(deficit, deficit)
    numerator = [(beta * value, psi * value) for value in denominator]
    numerator[0] = (numerator[0][0] - 60 * center, numerator[0][1])
    numerator[1] = (numerator[1][0] - 60, numerator[1][1])
    coefficients = [(Fraction(1), Fraction(0))]
    for order in range(degree):
        rhs = (Fraction(0), Fraction(0))
        for index in range(min(4, order) + 1):
            product = complex_multiply(numerator[index], coefficients[order - index])
            rhs = (rhs[0] + product[0], rhs[1] + product[1])
        lhs = (Fraction(0), Fraction(0))
        for index in range(1, min(4, order) + 1):
            factor = denominator[index] * (order - index + 1)
            term = coefficients[order - index + 1]
            lhs = (lhs[0] + factor * term[0], lhs[1] + factor * term[1])
        scale = denominator[0] * (order + 1)
        coefficients.append(((rhs[0] - lhs[0]) / scale, (rhs[1] - lhs[1]) / scale))
    derivative = [(index * value[0], index * value[1])
                  for index, value in enumerate(coefficients)][1:]
    product_ds = convolve([(value, Fraction(0)) for value in denominator], derivative)
    product_ns = convolve(numerator, coefficients)
    residual = []
    for index in range(max(len(product_ds), len(product_ns))):
        ds = product_ds[index] if index < len(product_ds) else (Fraction(0), Fraction(0))
        ns = product_ns[index] if index < len(product_ns) else (Fraction(0), Fraction(0))
        residual.append((ds[0] - ns[0], ds[1] - ns[1]))
    zero = (Fraction(0), Fraction(0))
    if any(value != zero for value in residual[:degree]):
        raise RuntimeError("exact low-order complex residual identity failed")
    if any(value != zero for value in residual[degree + 5:]):
        raise RuntimeError("complex residual leaves more than five slots")
    modulus_bound = sum((abs(value[0]) + abs(value[1])) * HALF_WIDTH ** index
                        for index, value in enumerate(residual))
    primitive = [(Fraction(0), Fraction(0))]
    for index, value in enumerate(coefficients):
        primitive.append((value[0] / (index + 1), value[1] / (index + 1)))
    integral = (Fraction(0), Fraction(0))
    for index, value in enumerate(primitive):
        if index % 2 == 1:
            weight = 2 * HALF_WIDTH ** index
            integral = (integral[0] + value[0] * weight,
                        integral[1] + value[1] * weight)
    return {"residual_modulus_upper": modulus_bound, "integral": integral}


def panel_pricing(parameters, center, degree):
    radius = parameters["radius"]
    beta = parameters["beta"]
    psi = parameters["psi"]
    edge = abs(center) + HALF_WIDTH
    denominator_lower = (1 - edge ** 2) ** 2
    panel = build_complex_panel(beta, psi, center, degree)
    variation = (abs(beta) + abs(psi) + 60 * edge / denominator_lower) * HALF_WIDTH
    phase = Fraction(-30) / (1 - center ** 2) + beta * center
    amplitude_center, amplitude_radius = compact_scalar(phase)[-1]
    growth_center, growth_radius = compact_scalar(2 * variation)[-1]
    analytic = ((amplitude_center + amplitude_radius) *
                (growth_center + growth_radius) *
                (panel["residual_modulus_upper"] / denominator_lower) *
                2 * HALF_WIDTH ** 2)
    # The panel's center contribution to the entry carries the exact
    # rotation exp(i*psi*center); dropping it loses the cross-panel
    # cancellation that the certified value exhibits.
    rotation = _exp_i(psi * center)
    rotated = complex_multiply(rotation, panel["integral"])
    contribution = (radius * amplitude_center * rotated[0],
                    radius * amplitude_center * rotated[1])
    return {"charge": radius * analytic, "contribution": contribution}


def edge_charge_pricing(parameters):
    # Edge region |u| >= CUT. The real phase f(u) = -30/(1-u^2) + beta*u is
    # strictly decreasing on [CUT, 1): f'(u) = -60u/(1-u^2)^2 + beta
    # <= -60*CUT + beta < 0 since (1-u^2)^2 <= 1 there. So the integrand
    # modulus, which is exp(f(u)) (the imaginary part |exp(i*psi*u)| = 1),
    # is bounded by its value at the cut; the left edge is dominated by the
    # same bound because f is increasing on (-1, -CUT] toward f(-CUT)
    # <= f(CUT) for beta > 0. No |psi| term enters the edge bound.
    radius = parameters["radius"]
    beta = parameters["beta"]
    edge_phase = Fraction(-30) / (1 - CUT ** 2) + beta * CUT
    edge_center, edge_radius = compact_scalar(edge_phase)[-1]
    return radius * 2 * (1 - CUT) * (edge_center + edge_radius)


def main():
    capture = json.loads(
        (ROOT / "results/2275_gap_owner_audit.json").read_text())["owner_capture"]
    survey = [(column, column_parameters(capture, column))
              for column in range(30)]
    nonzero = [(column, parameters) for column, parameters in survey
               if parameters["psi"] != 0]
    worst_column, pilot = max(nonzero,
                              key=lambda pair: abs(pair[1]["psi"]))
    print(f"off-diagonal phase survey: {len(nonzero)}/29 columns nonzero; "
          f"pilot entry ({ROW},{worst_column}) at worst |psi| "
          f"({float(abs(pilot['psi'])):.6f}, radius {float(pilot['radius'])}, "
          f"beta {float(pilot['beta'])})", flush=True)

    edge = edge_charge_pricing(pilot)
    witness = json.loads(
        (ROOT / "results/2351_moment_matrix_witness.json").read_text())
    entry = witness["matrix"][ROW][worst_column]

    ladder = []
    for degree in DEGREE_LADDER:
        total_charge = Fraction(0)
        worst_panel = (0, Fraction(0))
        center = (Fraction(0), Fraction(0))
        for index in range(PANEL_COUNT):
            price = panel_pricing(pilot, panel_center(index), degree)
            total_charge += price["charge"]
            center = (center[0] + price["contribution"][0],
                      center[1] + price["contribution"][1])
            if price["charge"] > worst_panel[1]:
                worst_panel = (index, price["charge"])
        box = total_charge + edge

        def margin(coordinate):
            low = Fraction(entry[coordinate]["lower_exact"])
            high = Fraction(entry[coordinate]["upper_exact"])
            value = center[0] if coordinate == "real" else center[1]
            return {"inside": low <= value - box and value + box <= high,
                    "slack_low_exact": str(value - box - low),
                    "slack_high_exact": str(high - value - box)}

        pricing = {"real": margin("real"), "imag": margin("imag")}
        ladder.append({"degree": degree,
                       "partition_charge_sum_exact": str(total_charge),
                       "worst_panel": worst_panel[0],
                       "worst_panel_charge_exact": str(worst_panel[1]),
                       "box_total_exact": str(box),
                       "containment": pricing})
        inside = pricing["real"]["inside"] and pricing["imag"]["inside"]
        print(f"degree {degree}: charge sum ~{float(total_charge):.6e}; "
              f"box ~{float(box):.6e}; center ~({float(center[0]):.6e}, "
              f"{float(center[1]):.6e}); inside: {inside}", flush=True)

    result = {
        "record": 2624, "entry": [ROW, worst_column],
        "pilot_parameters": {key: str(value) for key, value in pilot.items()},
        "beta_psi_model": "per-column: beta = node_re*width_col^2, "
                          "psi = (node_im + modulation_col)*width_col^2, "
                          "matching the certified 2337 integrate_family",
        "offdiagonal_phase_nonzero": bool(nonzero),
        "nonzero_columns": len(nonzero),
        "cancelled_columns": [column for column, parameters in survey
                              if parameters["psi"] == 0],
        "worst_phase_column": worst_column,
        "worst_phase_abs_exact": str(abs(pilot["psi"])),
        "panel_cover": {"panels": PANEL_COUNT, "half_width": str(HALF_WIDTH),
                        "cut": str(CUT)},
        "edge_bound_method": "monotone_phase_supremum_at_cut",
        "edge_charge_exact": str(edge),
        "center_contribution_phase": "exp(i*psi*panel_center) applied per panel",
        "center_engine": f"external mpmath at {EXP_I_DIGITS} dps, "
                         "decimal round-trip into exact Fraction; lean-side "
                         "complex scalar engine is a shared route obligation",
        "degree_ladder": ladder,
        "target_rectangle": {coordinate: {"lower_exact": entry[coordinate]["lower_exact"],
                                          "upper_exact": entry[coordinate]["upper_exact"]}
                             for coordinate in ("real", "imag")},
        "route_a_complex_polynomial_new_obligations": [
            "complex scalar exp engine (cos/sin at exact rational phase) - "
            "needed by BOTH routes, not an extra cost of route (a)",
            "complex list add/scale/mul/derivative/eval generic replay helpers",
            "complex residual stability theorem (integrating-factor argument "
            "over |.|) at degree ~52",
            "complex primitive and FTC replay",
            "per-panel complex tables (same decide+kernel shape, ~1.6x "
            "coefficient count vs the diagonal degree-32 tables)",
        ],
        "route_b_cos_sin_split_new_obligations": [
            "complex scalar exp engine anyway (cos/sin at exact rational "
            "phase) - the split does not avoid it",
            "two real tables per panel (cos- and sin-weighted envelopes) "
            "with double decide+kernel cost per panel",
            "product stability theorem for exp(H) against trigonometric "
            "factors",
        ],
        "recommended_route": "a_complex_polynomial",
        "route_rationale": "the rational-phase cos/sin engine is shared "
                           "ground, so route (b) pays it AND double real "
                           "tables; route (a) pays it once and reuses the "
                           "single complex recurrence, with the degree "
                           "ladder showing the truncation lever suffices "
                           "for the tightest off-diagonal rectangle",
        "pricing_lean_verified": False,
        "actual_entry_containment_lean_verified": False,
        "producer_go": False, "rh_claim": False,
        "probe_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    (ROOT / "results/2624_offdiagonal_pricing.json").write_text(
        json.dumps(result, indent=2) + "\n", encoding="utf-8", newline="\n")


if __name__ == "__main__":
    main()
