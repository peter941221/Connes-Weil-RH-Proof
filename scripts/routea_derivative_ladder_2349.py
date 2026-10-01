"""2349: exact bump recurrence and same-node-sum panel repricing."""
import argparse
from fractions import Fraction
import hashlib
import json
from math import comb
from pathlib import Path

from flint import arb, ctx

import routea_direct_ideal_strip_2342 as direct
import routea_one_sided_panel_transfer_2341 as panel

ROOT = Path(__file__).resolve().parents[1]
K = 30
MAX_ORDER = 4


def add_term(polynomial, power, coefficient):
    polynomial[power] = polynomial.get(power, 0) + coefficient
    if polynomial[power] == 0:
        del polynomial[power]


def next_numerator(polynomial, order):
    result = {}
    for power, coefficient in polynomial.items():
        add_term(result, power + 1, (-2 * K + 4 * order) * coefficient)
        add_term(result, power + 3, -4 * order * coefficient)
        if power:
            for shift, factor in ((-1, 1), (1, -2), (3, 1)):
                add_term(result, power + shift, factor * power * coefficient)
    return result


def get_numerators():
    numerators = [{0: 1}]
    for order in range(MAX_ORDER):
        numerators.append(next_numerator(numerators[-1], order))
    return numerators


def next_two_variable(polynomial):
    result = {}
    for (u_power, t_power), coefficient in polynomial.items():
        if u_power:
            add_term(result, (u_power - 1, t_power), u_power * coefficient)
        if t_power:
            add_term(result, (u_power + 1, t_power + 1), 2 * t_power * coefficient)
        add_term(result, (u_power + 1, t_power + 2), -2 * K * coefficient)
    return result


def get_two_variable_numerators():
    numerators = [{(0, 0): 1}]
    for _ in range(MAX_ORDER):
        numerators.append(next_two_variable(numerators[-1]))
    return numerators


def clear_denominator(polynomial, order):
    result = {}
    for (u_power, t_power), coefficient in polynomial.items():
        remaining = 2 * order - t_power
        if remaining < 0:
            raise ValueError("unexpected inverse-deficit degree")
        for index in range(remaining + 1):
            add_term(result, u_power + 2 * index,
                     coefficient * comb(remaining, index) * (-1)**index)
    return result


def get_constants():
    return [sum(abs(value) for value in numerator.values())
            for numerator in get_numerators()]


def get_ladder(families, coefficients, radii):
    if len(families) != len(coefficients) or len(families) != len(radii):
        raise ValueError("family/coefficient/radius length mismatch")
    if any(not radius > 0 for radius in radii):
        raise ValueError("nonpositive or unresolved support radius")
    bump_bounds = [constant * arb(-K).exp() for constant in get_constants()]
    bounds = [arb(0) for _ in range(MAX_ORDER + 1)]
    for (_, modulation), coefficient, radius in zip(families, coefficients, radii):
        for order in range(MAX_ORDER + 1):
            bounds[order] += abs(coefficient).upper() * sum(
                arb(comb(order, index)) * abs(modulation)**index
                * bump_bounds[order - index] / radius**(order - index)
                for index in range(order + 1))
    return bounds


def validate_parent(parent):
    if (parent.get("record") != 2342 or parent.get("nodes") != 120001
            or parent.get("precision_bits") != 192
            or parent.get("coordinates") != "exact rational uniform grid"
            or parent.get("coefficient_owner") != "2338 exact analytic finite-node solution rectangles"):
        raise ValueError("unexpected direct-source contract")
    if parent.get("source_sha256") != hashlib.sha256(Path(direct.__file__).read_bytes()).hexdigest():
        raise ValueError("direct-source hash mismatch")
    for name, digest in parent["input_sha256"].items():
        if hashlib.sha256((ROOT / name).read_bytes()).hexdigest() != digest:
            raise ValueError("direct input hash mismatch: " + name)
    for name, digest in parent["helper_sha256"].items():
        if hashlib.sha256((ROOT / "scripts" / name).read_bytes()).hexdigest() != digest:
            raise ValueError("direct helper hash mismatch: " + name)
    if [endpoint["sigma_exact"] for endpoint in parent["endpoints"]] != ["-1/2", "1/2"]:
        raise ValueError("missing or reordered signed endpoints")
    if Fraction(parent["frozen_pin_exact"]) != direct.PIN:
        raise ValueError("frozen pin mismatch")
    if any(parent.get(flag) is not False for flag in
           ("lean_certificate_imported", "healthy_detector_instantiated",
            "complete_signed_kernel_priced", "owner_transfer_to_live_consumer",
            "producer_go", "rh_claim")):
        raise ValueError("unexpected parent scope")


def run():
    parent_path = ROOT / "results/2342_direct_ideal_strip.json"
    parent = json.loads(parent_path.read_text())
    validate_parent(parent)
    ctx.prec = parent["precision_bits"]
    families, radii_exact, radii, coefficients, _ = direct.load_ideal_source()
    radius_exact = max(radii_exact)
    if str(radius_exact) != parent["support_radius_exact"]:
        raise ValueError("support-radius owner mismatch")
    radius = direct.certificate.lift_fraction(radius_exact)
    numerators = get_numerators()
    independent = get_two_variable_numerators()
    if any(clear_denominator(independent[order], order) != numerator
           for order, numerator in enumerate(numerators)):
        raise ValueError("independent exact recurrence mismatch")
    constants = get_constants()
    legacy = [1, 60, 3900, 245160, 696*K + 780*K**2 + 360*K**3 + 16*K**4]
    if not all(derived <= old for derived, old in zip(constants, legacy)):
        raise ValueError("legacy constants not covered by derived bounds")
    ladders = [get_ladder(families, coefficient, radii) for coefficient in coefficients]
    old_ladders = [direct.recomposed.ladder(families, coefficient, radii)
                   for coefficient in coefficients]
    endpoints = []
    for endpoint in parent["endpoints"]:
        sigma = direct.certificate.lift_fraction(Fraction(endpoint["sigma_exact"]))
        channels = {}
        for channel_index, name in enumerate(("base", "correction")):
            fields = {}
            for order, key in ((0, "m0"), (2, "d2")):
                old_fields = endpoint["channels"][name]
                old_panel = panel.get_panel_upper(old_ladders[channel_index], order, sigma,
                                                  radius, parent["nodes"])
                if Fraction(direct.certificate.serialize_real(old_panel)["upper_exact"]) != Fraction(old_fields[key + "_panel_upper"]["upper_exact"]):
                    raise ValueError("same-run old-panel reproduction failed")
                point_exact = Fraction(old_fields[key + "_point_upper"]["upper_exact"])
                point = direct.certificate.lift_fraction(point_exact)
                reproduced = direct.certificate.serialize_real((point + old_panel).upper())
                if Fraction(reproduced["upper_exact"]) != Fraction(old_fields[key]["upper_exact"]):
                    raise ValueError("same-run old-total reproduction failed")
                new_panel = panel.get_panel_upper(ladders[channel_index], order, sigma,
                                                  radius, parent["nodes"])
                new_total = direct.certificate.serialize_real((point + new_panel).upper())
                if Fraction(new_total["upper_exact"]) > Fraction(old_fields[key]["upper_exact"]):
                    raise ValueError("new total exceeds old bound")
                fields[key] = new_total
                fields[key + "_point_upper"] = old_fields[key + "_point_upper"]
                fields[key + "_panel_upper"] = direct.certificate.serialize_real(new_panel)
                fields[key + "_old_panel_upper"] = old_fields[key + "_panel_upper"]
            channels[name] = fields
        endpoints.append({"sigma_exact": endpoint["sigma_exact"], "channels": channels})
    maxima = {name: {key: max(Fraction(row["channels"][name][key]["upper_exact"])
                             for row in endpoints) for key in ("m0", "d2")}
              for name in ("base", "correction")}
    product = min(maxima["base"]["d2"] * maxima["correction"]["m0"],
                  maxima["correction"]["d2"] * maxima["base"]["m0"])
    old_maxima = {name: {key: max(Fraction(row["channels"][name][key]["upper_exact"])
                                 for row in parent["endpoints"]) for key in ("m0", "d2")}
                  for name in ("base", "correction")}
    old_product = min(old_maxima["base"]["d2"] * old_maxima["correction"]["m0"],
                      old_maxima["correction"]["d2"] * old_maxima["base"]["m0"])
    if old_product != Fraction(parent["continuum_min_product_upper_exact"]):
        raise ValueError("parent product mismatch")
    return {
        "record": 2349, "status": "EXACT_DERIVATIVE_RECURRENCE_EXTERNAL_REPRICE",
        "precision_bits": ctx.prec, "nodes": parent["nodes"],
        "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "parent_sha256": hashlib.sha256(parent_path.read_bytes()).hexdigest(),
        "parent_input_sha256": parent["input_sha256"],
        "parent_helper_sha256": parent["helper_sha256"],
        "numerators": [{str(power): value for power, value in sorted(numerator.items())}
                       for numerator in numerators],
        "derived_constants": constants, "legacy_constants": legacy,
        "independent_two_variable_recurrence_exact": True,
        "legacy_constants_dominate_derived": True,
        "same_run_old_panels_and_totals_exact": True,
        "support_radius_exact": str(radius_exact),
        "node_sums_reused_from": "results/2342_direct_ideal_strip.json",
        "node_sums_recomputed": False,
        "endpoints": endpoints,
        "continuum_min_product_upper_exact": str(product),
        "old_continuum_min_product_upper_exact": str(old_product),
        "frozen_pin_exact": str(direct.PIN), "fits_existing_pin": product < direct.PIN,
        "derivative_majorants_formalized_in_lean": False,
        "lean_certificate_imported": False, "healthy_detector_instantiated": False,
        "complete_signed_kernel_priced": False, "owner_transfer_to_live_consumer": False,
        "producer_go": False, "rh_claim": False}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=ROOT / "results/2349_derivative_ladder.json")
    arguments = parser.parse_args()
    result = run()
    arguments.output.write_text(json.dumps(result, indent=2) + "\n")
    print(result["derived_constants"], result["fits_existing_pin"],
          float(Fraction(result["continuum_min_product_upper_exact"])), flush=True)
