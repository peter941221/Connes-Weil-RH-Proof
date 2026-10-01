"""2342: independent Arb strip norms of the exact repaired finite-node source."""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path

import flint
from flint import acb, arb, ctx

import routea_marked_sign_arb_certificate_2337 as certificate
import routea_repair_norm_transfer_2339 as transfer
import routea_recomposed_point_panel_transfer_2340 as recomposed
import routea_one_sided_panel_transfer_2341 as panel

ROOT = Path(__file__).resolve().parents[1]
PIN = Fraction("2644542.8515")


def decode_real_rectangle(value):
    lower, upper = (Fraction(value[key]) for key in ("lower_exact", "upper_exact"))
    if lower > upper:
        raise ValueError("inverted coefficient rectangle")
    midpoint = certificate.lift_fraction((lower + upper) / 2)
    radius = certificate.lift_fraction((upper - lower) / 2).upper()
    return midpoint + arb(0, radius)


def decode_complex_rectangle(value):
    return acb(decode_real_rectangle(value["real"]),
               decode_real_rectangle(value["imag"]))


def load_ideal_source():
    relatives = ("results/2275_gap_owner_audit.json",
                 "results/2338_exact_interpolation_repair.json",
                 "scripts/routea_exact_interpolation_repair_2338.py",
                 "scripts/routea_marked_sign_arb_certificate_2337.py")
    for name in relatives:
        transfer.check_hash(ROOT / name, transfer.INPUT_HASHES[name])
    capture, families, _, _, _ = certificate.load_capture()
    repair = json.loads((ROOT / relatives[1]).read_text())
    rows = repair["coefficient_rows"]
    if len(rows) != 30 or [row["index"] for row in rows] != list(range(30)):
        raise ValueError("incomplete or reordered repaired coefficient rows")
    if repair.get("finite_node_realization_scope") != "unique coefficients of the exact analytic moment matrix":
        raise ValueError("unexpected repaired-source scope")
    if not Fraction(repair["neumann_defect_infinity_upper"]["upper_exact"]) < Fraction(1, 2):
        raise ValueError("repaired-source invertibility gate failed")
    widths = [Fraction(float.fromhex(width)) for width, _ in capture["families_hex"]]
    radii_exact = [width**2 for width in widths]
    radii = [certificate.lift_fraction(radius) for radius in radii_exact]
    coefficients = [[decode_complex_rectangle(row[key]) for row in rows]
                    for key in ("ideal_base_coefficient", "ideal_correction_coefficient")]
    return families, radii_exact, radii, coefficients, relatives


def evaluate_node(coordinate_exact, families, radii_exact, radii, coefficients):
    coordinate = certificate.lift_fraction(coordinate_exact)
    values = [acb(0) for _ in range(4)]
    for index, ((_, theta), radius_exact, radius) in enumerate(zip(families, radii_exact, radii)):
        if abs(coordinate_exact) >= radius_exact:
            continue
        ratio = coordinate / radius
        denominator = 1 - ratio**2
        if not denominator > 0:
            raise ValueError("precision insufficient to separate an interior point from the edge")
        inverse = 1 / denominator
        first = -60 * ratio * inverse**2 / radius
        second = -60 * (inverse**2 + 4 * ratio**2 * inverse**3) / radius**2
        bump = (-30 * inverse).exp()
        carrier = acb(0, theta * coordinate).exp()
        function_value = bump * carrier
        derivative_factor = acb(second + first**2 - theta**2, 2 * theta * first)
        for channel in range(2):
            term = coefficients[channel][index] * function_value
            values[2 * channel] += term
            values[2 * channel + 1] += term * derivative_factor
    if not all(value.is_finite() for value in values):
        raise ValueError("nonfinite node enclosure")
    return values


def run(nodes, precision):
    if nodes < 3 or nodes % 2 == 0 or precision < 128:
        raise ValueError("odd node count >= 3 and at least 128 precision bits required")
    ctx.prec = precision
    families, radii_exact, radii, coefficients, relatives = load_ideal_source()
    radius_exact = max(radii_exact)
    radius = certificate.lift_fraction(radius_exact)
    step = certificate.lift_fraction(2 * radius_exact / (nodes - 1))
    accumulators = [[arb(0) for _ in range(4)] for _ in range(2)]
    controls = []
    control_indices = {0, nodes // 4, nodes // 2, 3 * nodes // 4, nodes - 1}
    for index in range(nodes):
        coordinate_exact = -radius_exact + 2 * radius_exact * index / (nodes - 1)
        values = evaluate_node(coordinate_exact, families, radii_exact, radii, coefficients)
        magnitudes = [abs(value).upper() for value in values]
        coordinate = certificate.lift_fraction(coordinate_exact)
        weights = [(-coordinate / 2).exp(), (coordinate / 2).exp()]
        trapezoid_weight = 1 if index in (0, nodes - 1) else 2
        for side in range(2):
            for slot in range(4):
                accumulators[side][slot] += trapezoid_weight * weights[side] * magnitudes[slot]
        if index in control_indices:
            controls.append({"index": index, "coordinate_exact": str(coordinate_exact),
                             "values": [certificate.serialize_complex(value) for value in values]})
        if index % 10000 == 0:
            print(f"2342 node {index}/{nodes}", flush=True)
    ladders = [recomposed.ladder(families, coefficient, radii) for coefficient in coefficients]
    endpoints = []
    for side, sigma in enumerate((arb("-1/2"), arb("1/2"))):
        channels = {}
        for channel, name in enumerate(("base", "correction")):
            fields = {}
            for offset, order, key in ((0, 0, "m0"), (1, 2, "d2")):
                point = (step * accumulators[side][2 * channel + offset] / 2).upper()
                remainder = panel.get_panel_upper(ladders[channel], order, sigma, radius, nodes)
                fields[key] = certificate.serialize_real((point + remainder).upper())
                fields[key + "_point_upper"] = certificate.serialize_real(point)
                fields[key + "_panel_upper"] = certificate.serialize_real(remainder)
            channels[name] = fields
        endpoints.append({"sigma_exact": str(Fraction(-1 if side == 0 else 1, 2)),
                          "channels": channels})
    maxima = {name: {key: max(Fraction(row["channels"][name][key]["upper_exact"])
                             for row in endpoints) for key in ("m0", "d2")}
              for name in ("base", "correction")}
    product = min(maxima["base"]["d2"] * maxima["correction"]["m0"],
                  maxima["correction"]["d2"] * maxima["base"]["m0"])
    return {"record": 2342, "status": "DIRECT_IDEAL_STRIP_EXTERNAL_ENCLOSURE",
            "python_flint_version": flint.__version__, "precision_bits": precision, "nodes": nodes,
            "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "input_sha256": {name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest() for name in relatives},
            "helper_sha256": {Path(module.__file__).name: hashlib.sha256(Path(module.__file__).read_bytes()).hexdigest()
                              for module in (certificate, transfer, recomposed, panel)},
            "support_radius_exact": str(radius_exact), "coordinates": "exact rational uniform grid",
            "coefficient_owner": "2338 exact analytic finite-node solution rectangles",
            "legacy_2303_point_sums_used": False, "zero_count_used": False,
            "nodal_chain": "Arb/Acb outward balls from exact rational coordinates and repaired coefficient rectangles",
            "continuum_sigma_rule": "convex weighted norms <= maximum of endpoint norms on [-1/2,1/2]",
            "endpoints": endpoints, "node_controls": controls,
            "continuum_min_product_upper_exact": str(product), "frozen_pin_exact": str(PIN),
            "fits_existing_pin": product < PIN,
            "lean_certificate_imported": False, "healthy_detector_instantiated": False,
            "complete_signed_kernel_priced": False, "owner_transfer_to_live_consumer": False,
            "producer_go": False, "rh_claim": False}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--nodes", type=int, default=120001)
    parser.add_argument("--precision", type=int, default=192)
    parser.add_argument("--output", type=Path, default=ROOT / "results/2342_direct_ideal_strip.json")
    arguments = parser.parse_args()
    result = run(arguments.nodes, arguments.precision)
    arguments.output.write_text(json.dumps(result, indent=2) + "\n")
    print(result["fits_existing_pin"], result["continuum_min_product_upper_exact"], flush=True)
