"""2341: one-sided panel repricing conditional on the 2303 node uppers."""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path

from flint import arb, ctx
import numpy as np

import routea_recomposed_point_panel_transfer_2340 as recomposed
import routea_repair_norm_transfer_2339 as transfer

ROOT = Path(__file__).resolve().parents[1]


def get_coordinate_gap(radius, count):
    if count < 2 or radius <= 0:
        raise ValueError("positive radius and at least two nodes required")
    grid = np.linspace(-radius, radius, count)
    exact_radius = Fraction(radius)
    return max(abs(Fraction(float(value)) -
                   (-exact_radius + 2 * exact_radius * index / (count - 1)))
               for index, value in enumerate(grid))


def get_weighted_derivative_upper(ladder, order, sigma, radius):
    return ((abs(sigma) * radius).exp() *
            (ladder[order + 1] + abs(sigma) * ladder[order])).upper()


def get_panel_upper(ladder, order, sigma, radius, count):
    if count < 2 or radius <= 0:
        raise ValueError("positive radius and at least two nodes required")
    step = 2 * radius / (count - 1)
    curvature = (abs(sigma) * radius).exp() * (
        ladder[order + 2] + 2 * abs(sigma) * ladder[order + 1]
        + sigma**2 * ladder[order])
    return (step**2 * (2 * radius) * curvature / 12).upper()


def validate_node_sum(source, point, count):
    if (point.get("record") != 2303 or point.get("mode") != "sigma"
            or point.get("sigma_index") != source["j"] or point.get("nodes") != count
            or point.get("values") != source["point"]
            or point.get("sigma") != source["sigma"]):
        raise ValueError("baseline node-sum provenance mismatch")


def run():
    ctx.prec = 320
    paths = {"baseline": ROOT / "results/2303_corrected_strip_envelope.json",
             "recomposed": ROOT / "results/2340_recomposed_point_panel_transfer.json",
             "repair": ROOT / "results/2338_exact_interpolation_repair.json"}
    baseline = json.loads(paths["baseline"].read_text())
    previous = json.loads(paths["recomposed"].read_text())
    if previous["source_sha256"] != hashlib.sha256(Path(recomposed.__file__).read_bytes()).hexdigest():
        raise ValueError("2340 source hash mismatch")
    recomposed.validate_baseline_contract(baseline)
    for name, digest in transfer.INPUT_HASHES.items():
        transfer.check_hash(ROOT / name, digest)
    capture, families, coefficients, _, _ = transfer.certificate.load_capture()
    radii = [transfer.certificate.lift_float(float.fromhex(width)**2)
             for width, _ in capture["families_hex"]]
    radius_float = baseline["owner"]["rmax"]
    radius = transfer.certificate.lift_float(radius_float)
    if any(family_radius > radius for family_radius in radii):
        raise ValueError("baseline support radius does not cover the stored families")
    count = baseline["grid"]["x_nodes"]
    if count != 240001:
        raise ValueError("unexpected baseline spatial grid")
    ladders = {channel: recomposed.ladder(families, coefficient, radii)
               for channel, coefficient in zip(("base", "correction"), coefficients)}
    coordinate_gap = get_coordinate_gap(radius_float, count)
    old_rows = {row["j"]: row for row in previous["rows"]}
    if len(previous["rows"]) != 101 or set(old_rows) != set(range(-50, 51)):
        raise ValueError("incomplete 2340 sigma rows")
    rows, point_files = [], []
    for source in baseline["grid_rows"]:
        point_path = ROOT / f"results/2303_sigma_{source['j']}.json"
        point = json.loads(point_path.read_text())
        validate_node_sum(source, point, count)
        point_files.append({"name": point_path.name,
                            "sha256": hashlib.sha256(point_path.read_bytes()).hexdigest()})
        sigma = transfer.certificate.lift_float(source["sigma"])
        weight = (abs(transfer.lift(Fraction(source["j"], 100)) - sigma)
                  * transfer.lift(Fraction(radius_float))).exp()
        channels = {}
        for channel, prefix in (("base", "base"), ("correction", "corr")):
            values = {}
            for order, name in ((0, "M0"), (2, "D2")):
                panel = get_panel_upper(ladders[channel], order, sigma, radius, count)
                old_panel = transfer.certificate.lift_float(source["panel"][prefix + "_" + name])
                extra_panel = max(arb(0), (panel - old_panel).upper())
                geometry = (2 * radius * transfer.lift(coordinate_gap)
                            * get_weighted_derivative_upper(ladders[channel], order, sigma, radius)).upper()
                key = "m0" if order == 0 else "d2"
                old_upper = transfer.lift(Fraction(old_rows[source["j"]]["channels"][channel][key]["upper_exact"]))
                values[key] = (old_upper + weight * (extra_panel + geometry)).upper()
                values[key + "_directed_panel"] = panel
                values[key + "_panel_topup"] = extra_panel
                values[key + "_coordinate_charge"] = geometry
            channels[channel] = values
        bound = min((channels["base"]["d2"] * channels["correction"]["m0"]).upper(),
                    (channels["correction"]["d2"] * channels["base"]["m0"]).upper())
        rows.append({"j": source["j"], "channels": {
            channel: {key: recomposed.ep(value) for key, value in values.items()}
            for channel, values in channels.items()},
            "min_product_upper": recomposed.ep(bound),
            "fits_existing_pin": bool(bound < transfer.lift(recomposed.PIN))})
    maximum = max(rows, key=lambda row: Fraction(row["min_product_upper"]["upper_exact"]))
    return {"record": 2341, "status": "ONE_SIDED_PANEL_TRANSFER_CONDITIONAL_ON_NODE_UPPERS",
            "precision_bits": ctx.prec,
            "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "helper_source_sha256": {
                Path(module.__file__).name: hashlib.sha256(Path(module.__file__).read_bytes()).hexdigest()
                for module in (recomposed, transfer, transfer.certificate)},
            "input_sha256": {key: hashlib.sha256(path.read_bytes()).hexdigest()
                             for key, path in paths.items()},
            "node_sum_provenance": point_files,
            "coordinate_gap_exact": str(coordinate_gap),
            "zero_count_used_by_new_panel_law": False,
            "point_node_upper_theorem_proved": False,
            "coordinate_grid_identity_with_original_run_proved": False,
            "transfer_theorem_imported_in_lean": False,
            "owner_transfer_to_live_consumer": False, "producer_go": False, "rh_claim": False,
            "all_nodes_fit_existing_pin": all(row["fits_existing_pin"] for row in rows),
            "maximum_node": maximum["j"], "maximum_min_product_upper": maximum["min_product_upper"],
            "rows": rows}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path,
                        default=ROOT / "results/2341_one_sided_panel_transfer.json")
    arguments = parser.parse_args()
    result = run()
    arguments.output.write_text(json.dumps(result, indent=2) + "\n")
    print(result["all_nodes_fit_existing_pin"], result["maximum_min_product_upper"]["display"])
