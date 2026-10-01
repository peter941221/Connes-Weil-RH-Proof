"""2353: directed finite controls and analytic full-tail suppliers for the repaired owner."""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path

from flint import acb, arb, ctx

import routea_derivative_ladder_2349 as ladder
import routea_direct_ideal_strip_2342 as direct
import routea_marked_sign_arb_certificate_2337 as certificate
import routea_same_owner_premise_audit_2352 as premise

ROOT = Path(__file__).resolve().parents[1]
BOUND = Fraction(1, 2)
CONTOUR_EDGE_DELTA = Fraction(1, 8)
BASELINE_CONTOUR_EDGE_DELTA = Fraction(1, 64)
CONTOUR_SHIFT = Fraction(1, 2)
CONTOUR_CELLS = 64
STRONG_BOUND = Fraction(1, 2**14)


def get_family_budgets(radii, coefficients):
    constants = ladder.get_constants()
    if constants != [1, 60, 3720, 236160, 15130080]:
        raise ValueError("unexpected actual derivative ladder")
    if len(radii) != len(coefficients) or not radii or any(radius <= 0 for radius in radii):
        raise ValueError("invalid family budget dimensions or radii")
    rows = []
    for radius_exact, coefficient in zip(radii, coefficients):
        radius = certificate.lift_fraction(radius_exact)
        mass = 2 * radius * radius.exp() * abs(coefficient) * arb(-30).exp()
        if not mass.is_finite():
            raise ValueError("nonfinite coefficient magnitude budget")
        rows.append({str(order): Fraction(str((mass * constants[order] / radius**order).upper().fmpq()))
                     for order in (0, 2, 4)})
    return rows


def get_tail_upper(budgets, modulations, threshold):
    threshold = Fraction(threshold)
    if threshold < 0 or len(budgets) != len(modulations):
        raise ValueError("invalid tail threshold or dimensions")
    total = Fraction(0)
    for row, modulation in zip(budgets, modulations):
        delta = threshold - abs(modulation)
        candidates = [row["0"]]
        if delta > 0:
            candidates += [row[str(order)] / delta**order for order in (2, 4)]
        total += min(candidates)
    return total


def get_contour_family_bounds(radii, modulations, coefficients, threshold,
                             cells=CONTOUR_CELLS, shift=CONTOUR_SHIFT, edge_delta=CONTOUR_EDGE_DELTA):
    threshold, shift, edge_delta = Fraction(threshold), Fraction(shift), Fraction(edge_delta)
    if not radii or len(radii) != len(modulations) or len(radii) != len(coefficients):
        raise ValueError("contour family dimensions do not match")
    if threshold < 0 or shift <= 0 or not 0 < edge_delta < 1 or not isinstance(cells, int) or cells <= 0:
        raise ValueError("invalid contour geometry")
    cut_exact = 1 - edge_delta
    cut = certificate.lift_fraction(cut_exact)
    rows = []
    for radius_exact, modulation, coefficient in zip(radii, modulations, coefficients):
        if radius_exact <= 0 or threshold <= abs(modulation):
            raise ValueError("contour damping requires positive radius and separated carrier")
        radius = certificate.lift_fraction(radius_exact)
        gap_exact = threshold - abs(modulation)
        damping = radius * certificate.lift_fraction(gap_exact)
        top = radius * 2 * cut * (radius * cut - damping * certificate.lift_fraction(shift)).exp()
        vertical = arb(0)
        for index in range(cells):
            lower = shift * index / cells
            upper = shift * (index + 1) / cells
            coordinate = direct.decode_real_rectangle({"lower_exact": str(lower), "upper_exact": str(upper)})
            real_denominator = 1 - cut**2 + coordinate**2
            denominator_norm_square = real_denominator**2 + 4 * cut**2 * coordinate**2
            if not real_denominator > 0 or not denominator_norm_square > 0:
                raise ValueError("contour enclosure does not exclude singularities")
            inverse_real = real_denominator / denominator_norm_square
            amplitude = (-30 * inverse_real - damping * coordinate).exp()
            vertical += certificate.lift_fraction(upper - lower) * amplitude.upper()
        connectors = radius * ((radius * cut).exp() + 1) * vertical
        edge = 2 * certificate.lift_fraction(edge_delta) * radius * (
            -30 / certificate.lift_fraction(edge_delta * (2 - edge_delta)) + radius).exp()
        magnitude = abs(coefficient)
        terms = {name: Fraction(str((magnitude * value).upper().fmpq()))
                 for name, value in (("top", top), ("connectors", connectors), ("edge", edge))}
        rows.append({"carrier_gap_exact": str(gap_exact),
                     "top_upper_exact": str(terms["top"]),
                     "connector_upper_exact": str(terms["connectors"]),
                     "edge_upper_exact": str(terms["edge"]),
                     "total_upper_exact": str(sum(terms.values()))})
    return rows


def get_whole_line_constant(budgets, modulations, order):
    if order not in (2, 4) or len(budgets) != len(modulations):
        raise ValueError("invalid whole-line order or dimensions")
    return sum(max((2 * abs(modulation))**order * row["0"], 2**order * row[str(order)])
               for row, modulation in zip(budgets, modulations))


def get_threshold_ladder(budgets, modulations, start=128, bound=BOUND, steps=16):
    if not isinstance(start, int) or isinstance(start, bool) or start <= 0 or bound <= 0 or steps <= 0:
        raise ValueError("invalid contraction ladder")
    rows = []
    for index in range(steps):
        threshold = start * 2**index
        upper = get_tail_upper(budgets, modulations, threshold)
        rows.append({"threshold_exact": str(threshold), "upper_exact": str(upper),
                     "fits_bound": upper <= bound})
        if upper <= bound:
            return rows
    raise RuntimeError("registered finite analytic ladder did not certify contraction")


def classify_point(value, bound=BOUND):
    lower, upper = (Fraction(value[key]) for key in ("lower_exact", "upper_exact"))
    if lower > upper:
        raise ValueError("inverted point modulus bounds")
    if lower > bound:
        return "POINT_REFUTES_REGISTERED_UNIFORM_BOUND"
    if upper <= bound:
        return "POINT_ONLY_BELOW_BOUND"
    return "POINT_UNRESOLVED"


def get_healthy_shell_for_threshold(threshold, rho_height):
    threshold, rho_height = Fraction(threshold), abs(Fraction(rho_height))
    if threshold < 0:
        raise ValueError("negative actual tail threshold")
    shell = 0
    while 2**(shell + 1) < threshold or 2**(shell + 1) < 2 * rho_height:
        shell += 1
    return {"minimum_shell_index": shell, "ceiling_exact": str(2**(shell + 1)),
            "conditions": "T <= 2^(N+1), 2*abs(Im rho) <= 2^(N+1)",
            "complete_zero_prefix_proved": False}


def evaluate_point(families, coefficients, sigma, height, panels):
    source_point = acb(certificate.lift_fraction(sigma), certificate.lift_fraction(height))
    totals = [acb(0), acb(0)]
    edge_totals = [arb(0), arb(0)]
    for index, (width, modulation) in enumerate(families):
        value, edge = certificate.integrate_family(width, modulation, source_point, panels=panels)
        for channel in range(2):
            totals[channel] += coefficients[channel][index] * value
            edge_totals[channel] += abs(coefficients[channel][index]) * edge
    if not all(value.is_finite() for value in totals):
        raise RuntimeError("nonfinite actual source point")
    return {"sigma_exact": str(sigma), "height_exact": str(height),
            "values": [certificate.serialize_complex(value) for value in totals],
            "moduli": [certificate.serialize_real(abs(value)) for value in totals],
            "weighted_edge_charges": [certificate.serialize_real(value) for value in edge_totals]}


def run(precision=256, panels=16):
    if precision < 192 or panels < 8:
        raise ValueError("registered precision/panel minima not met")
    ctx.prec = precision
    parent = premise.run()
    families, radii_exact, _, coefficients, _ = direct.load_ideal_source()
    capture = json.loads((ROOT / "results/2275_gap_owner_audit.json").read_text())["owner_capture"]
    modulations = [premise.moment.hex_fraction(pair[1]) for pair in capture["families_hex"]]
    for (width, _), radius in zip(families, radii_exact):
        if not (width * width - certificate.lift_fraction(radius)).is_zero():
            raise ValueError("integrator radius differs from exact stored-width square")
    budgets = [get_family_budgets(radii_exact, values) for values in coefficients]
    threshold_rows = get_threshold_ladder(budgets[0], modulations)
    contour_rows = [get_contour_family_bounds(radii_exact, modulations, values, 128)
                    for values in coefficients]
    baseline_contour_rows = [get_contour_family_bounds(radii_exact, modulations, values, 128,
                                                      edge_delta=BASELINE_CONTOUR_EDGE_DELTA)
                             for values in coefficients]
    contour_base_upper = sum(min(Fraction(row["total_upper_exact"]), Fraction(baseline["total_upper_exact"]))
                             for row, baseline in zip(contour_rows[0], baseline_contour_rows[0]))
    chosen = Fraction(128) if contour_base_upper <= BOUND else Fraction(threshold_rows[-1]["threshold_exact"])
    chosen_bound = STRONG_BOUND if chosen == 128 and contour_base_upper <= STRONG_BOUND else BOUND
    controls = [evaluate_point(families, coefficients, Fraction(sigma), Fraction(height), panels)
                for sigma in (0, Fraction(1, 2), 1) for height in (128, -128)]
    for row in controls:
        row["base_verdict"] = classify_point(row["moduli"][0])
    rho_real = Fraction(parent["mandatory_targets"]["rho_real_exact"])
    rho_height = Fraction(parent["mandatory_targets"]["rho_imag_exact"])
    interpolation_control = evaluate_point(families, coefficients, rho_real, rho_height, panels)
    base_rectangle, correction_rectangle = interpolation_control["values"]
    for value in (base_rectangle, correction_rectangle):
        if not (Fraction(value["real"]["lower_exact"]) <= 1 <= Fraction(value["real"]["upper_exact"])
                and Fraction(value["imag"]["lower_exact"]) <= 0 <= Fraction(value["imag"]["upper_exact"])):
            raise ValueError("same-owner interpolation control excludes its exact target")
    sources = ["scripts/routea_same_owner_tail_supplier_2353.py",
               "scripts/routea_marked_sign_arb_certificate_2337.py",
               "scripts/routea_direct_ideal_strip_2342.py",
               "scripts/routea_derivative_ladder_2349.py",
               "scripts/routea_same_owner_premise_audit_2352.py",
               "ConnesWeilRH/Dev/C1RouteAOwnerDerivativeBudget.lean",
               "ConnesWeilRH/Dev/C1RouteAContourTail.lean",
               "ConnesWeilRH/Dev/C1RouteAContourTailAudit.lean"]
    return {"record": 2353, "status": "EXTERNAL_ANALYTIC_TAIL_SUPPLIER_WITH_DIRECTED_POINT_CONTROLS",
            "python_flint_version": certificate.flint.__version__,
            "precision_bits": precision, "panels": panels, "source_slab_exact": ["0", "1"],
            "frequency_convention": "raw source z = sigma + i*t; t is angular height, not xi",
            "source_sha256": {relative: hashlib.sha256((ROOT / relative).read_bytes()).hexdigest()
                              for relative in sources},
            "input_sha256": {relative: hashlib.sha256((ROOT / relative).read_bytes()).hexdigest()
                             for relative in ("results/2275_gap_owner_audit.json",
                                              "results/2338_exact_interpolation_repair.json",
                                              "results/2351_moment_matrix_witness.json")},
            "original_moment_witness_rechecked_same_run": True,
            "actual_integrator_radii_exact": True, "coefficient_rectangles_unchanged": True,
            "family_budgets_exact": [{str(index): {order: str(value) for order, value in row.items()}
                                      for index, row in enumerate(channel)} for channel in budgets],
            "base_contraction_threshold_ladder": threshold_rows,
            "base_contraction_threshold_ladder_method": "zeroth/second/fourth integration-by-parts bounds only",
            "ibp_only_base_threshold_exact": threshold_rows[-1]["threshold_exact"],
            "contour_geometry": {"edge_delta_exact": str(CONTOUR_EDGE_DELTA), "shift_exact": str(CONTOUR_SHIFT),
                                 "vertical_cells": CONTOUR_CELLS, "cut_exact": str(1 - CONTOUR_EDGE_DELTA)},
            "direct_integrator_edge_delta_exact": str(certificate.EDGE_DELTA),
            "contour_family_bounds_T128": contour_rows,
            "baseline_contour_geometry": {"edge_delta_exact": str(BASELINE_CONTOUR_EDGE_DELTA),
                                          "shift_exact": str(CONTOUR_SHIFT), "vertical_cells": CONTOUR_CELLS},
            "baseline_contour_family_bounds_T128": baseline_contour_rows,
            "baseline_contour_base_upper_T128_exact": str(sum(
                Fraction(row["total_upper_exact"]) for row in baseline_contour_rows[0])),
            "contour_bound_combination": "per-family minimum of two valid rectangle-and-real-edge bounds",
            "contour_base_upper_T128_exact": str(contour_base_upper),
            "T128_q_2neg14_proved": contour_base_upper <= STRONG_BOUND,
            "certified_base_threshold_exact": str(chosen), "certified_base_q_exact": str(chosen_bound),
            "supplier_scope": "all sigma in [0,1], both signs and all abs(t)>=T; conditional on actual coefficient-box membership",
            "whole_line_angular_constants_exact": {
                "base_order4": str(get_whole_line_constant(budgets[0], modulations, 4)),
                "correction_order2": str(get_whole_line_constant(budgets[1], modulations, 2))},
            "tail_consumer_normalization": "C4=D4/(2*pi)^4; C2=D2/(2*pi)^2; (2*pi)^12 cancels in (C4*C2)^2",
            "point_controls_T128": controls,
            "T128_q_half_refuted_by_point": any(row["base_verdict"] == "POINT_REFUTES_REGISTERED_UNIFORM_BOUND"
                                                for row in controls),
            "T128_uniform_bound_proved": min(Fraction(threshold_rows[0]["upper_exact"]), contour_base_upper) <= BOUND,
            "interpolation_control": interpolation_control,
            "minimum_healthy_shell_at_certified_threshold": get_healthy_shell_for_threshold(chosen, rho_height),
            "actual_numeric_coefficients_imported_in_lean": False,
            "tail_supplier_imported_in_lean": False, "actual_gate_row_paired": False,
            "fourth_order_spectral_tail_instantiated": False, "rho_is_source_zero_proved": False,
            "complete_zero_prefix_instantiated": False, "full_signed_kernel_priced": False,
            "healthy_detector_instantiated": False, "owner_changed": False,
            "map103_reopened": False, "producer_go": False, "rh_claim": False}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--precision", type=int, default=256)
    parser.add_argument("--panels", type=int, default=16)
    parser.add_argument("--output", type=Path, default=ROOT / "results/2353_same_owner_tail_supplier.json")
    arguments = parser.parse_args()
    result = run(arguments.precision, arguments.panels)
    arguments.output.write_text(json.dumps(result, indent=2) + "\n")
    print(result["status"], "T", result["certified_base_threshold_exact"],
          "T128 refuted", result["T128_q_half_refuted_by_point"], flush=True)
