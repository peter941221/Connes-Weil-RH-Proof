"""Exact arithmetic, predecessor and axiom controls for record 2574."""
import argparse
import copy
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

import validate_decomposed_correction_grid_2573 as controls
import price_second_chord_grid_2574 as pricing

ROOT = Path(__file__).resolve().parents[1]
FALSE_FLAGS = ("lean_certificate", "table_rounding_priced", "exact_coefficient_membership",
               "producer_go", "rh_claim")



def endpoint_controls():
    controls.ctx.prec = 192
    controls.mp.mp.dps = 90
    families = pricing.previous.load_families()
    rows = json.loads(pricing.previous.base.REPAIR.read_text())["coefficient_rows"]
    step = 2 * pricing.previous.base.RADIUS / pricing.previous.PRODUCTION_CELLS
    checks = 0
    for sign in (-1, 1):
        sigma = Fraction(sign, 2)
        for index in (0, 2700, 5120, 7540, 10240):
            position = -pricing.previous.base.RADIUS + index * step
            signed_sum = controls.mp.mpc(0)
            error_sum = controls.mp.mpf(0)
            for family, row in zip(families, rows):
                if abs(position) >= family["r"]:
                    continue
                box = row["ideal_correction_coefficient"]
                center = controls.mp.mpc(*[
                    controls.mp_exact((Fraction(box[part]["lower_exact"]) +
                                       Fraction(box[part]["upper_exact"])) / 2)
                    for part in ("real", "imag")])
                radius = controls.mp_exact(family["r"])
                modulation = controls.mp_exact(family["theta_exact"])
                def atom(value):
                    return controls.mp.exp(-30 / (1 - (value / radius) ** 2) +
                                           (controls.mp_exact(sigma) + 1j * modulation) * value)
                second = controls.mp.diff(atom, controls.mp_exact(position), 2)
                signed_sum += center * second
                error_sum += controls.mp_exact(pricing.previous.ERROR) * abs(second)
            expected = abs(signed_sum) + error_sum
            observed = controls.mp_exact(pricing.second_point(families, position, sigma))
            assert observed >= expected, (sign, index, str(observed - expected))
            checks += 1
    return dict(endpoint_checks=checks, includes_support_edges=True,
                sampled_controls_not_full_table_certificate=True)


def validate_payload(payload):
    assert payload["record"] == 2574
    assert payload["status"] == "EXTERNAL_SECOND_CHORD_GRID_PRICE"
    assert payload["coefficient_row"] == "ideal_correction_coefficient"
    assert Fraction(payload["error"]) == pricing.previous.ERROR
    assert Fraction(payload["pin"]) == pricing.previous.PIN
    for key in FALSE_FLAGS:
        assert payload[key] is False, key
    rows = payload["rows"]
    assert [row["sign"] for row in rows] == [-1, 1]
    cells = rows[0]["cells"]
    assert cells > 0 and all(row["cells"] == cells for row in rows)
    assert payload["production_grid"] == (cells == pricing.previous.PRODUCTION_CELLS)
    predecessor = json.loads((ROOT / f"results/2573_decomposed_grid_{cells}.json").read_text())
    controls.validate_payload(predecessor)
    assert payload["old_rows"] == predecessor["rows"]
    assert payload["predecessor_same_run"] == "ALL_ROW_FIELDS_EXACTLY_REPRODUCED"
    step = 2 * pricing.previous.base.RADIUS / cells
    for row, old_row in zip(rows, predecessor["rows"]):
        exact = {key: Fraction(value) for key, value in row["exact"].items()}
        old = {key: Fraction(value) for key, value in old_row["exact"].items()}
        assert all(value >= 0 for value in exact.values())
        assert exact["fourth_remainder"] == step ** 3 / 12 * old["fourth"]
        assert exact["second_piece"] == exact["second_node"] + exact["fourth_remainder"]
        assert exact["first_piece"] == old["first_piece"]
        assert exact["value_piece"] == old["value_piece"]
        assert exact["total"] == sum(exact[key] for key in
                                     ("second_piece", "first_piece", "value_piece"))
        assert Fraction(row["margin"]) == pricing.previous.PIN - exact["total"]
        assert row["fits_pin"] == (exact["total"] <= pricing.previous.PIN)
        assert Fraction(row["old_total"]) == old["total"]
        assert row["gain"] == float(old["total"] / exact["total"])
        for key, value in exact.items():
            assert row["display"][key] == float(value)
    assert payload["analytic_grid_fits"] == all(row["fits_pin"] for row in rows)
    for relative, expected in payload["source_sha256"].items():
        path = ROOT / relative
        assert path.resolve().is_relative_to(ROOT.resolve())
        assert hashlib.sha256(path.read_bytes()).hexdigest() == expected, relative


def mutation_controls(payload):
    rejected = []
    for name, change in (
        ("zero_total", lambda data: data["rows"][0]["exact"].update(total="0")),
        ("zero_remainder", lambda data: data["rows"][0]["exact"].update(fourth_remainder="0")),
        ("missing_sign", lambda data: data.update(rows=data["rows"][:1])),
        ("wrong_owner", lambda data: data.update(coefficient_row="ideal_base_coefficient")),
        ("false_membership", lambda data: data.update(exact_coefficient_membership=True)),
        ("false_lean_certificate", lambda data: data.update(lean_certificate=True)),
        ("predecessor_drift", lambda data: data["old_rows"][0]["exact"].update(total="0")),
    ):
        changed = copy.deepcopy(payload)
        change(changed)
        try:
            validate_payload(changed)
        except AssertionError:
            rejected.append(name)
        else:
            raise AssertionError(f"mutation accepted: {name}")
    return rejected


def check_build(log_path, mirror):
    text = log_path.read_text()
    assert "Build completed successfully" in text
    assert not re.search(r"^error:", text, re.MULTILINE)
    assert not re.search(r"\bsorry(?:Ax)?\b", text)
    source = ROOT / "ConnesWeilRH/Dev/C1RouteACorrectionSecondChord2574.lean"
    audit = ROOT / "ConnesWeilRH/Dev/C1RouteACorrectionSecondChord2574Audit.lean"
    names = re.findall(r"^theorem (\w+)", source.read_text(), re.MULTILINE)
    readings = dict(re.findall(r"'ConnesWeilRH.Dev.(\w+)' depends on axioms: \[(.*?)\]", text,
                               re.DOTALL))
    assert len(names) == 6
    for name in names:
        assert re.sub(r"\s+", " ", readings.get(name, "")) == (
            "propext, Classical.choice, Quot.sound"), name
    for path in (source, audit):
        assert path.read_bytes() == (mirror / path.relative_to(ROOT)).read_bytes()
    return dict(expected_targets=names, verified_targets=len(names),
                axiom_trio=True, source_mirror_equal=True,
                log_sha256=hashlib.sha256(log_path.read_bytes()).hexdigest(),
                source_sha256={str(path.relative_to(ROOT)):
                               hashlib.sha256(path.read_bytes()).hexdigest()
                               for path in (source, audit)})


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--cells", type=int, default=pricing.previous.PRODUCTION_CELLS)
    parser.add_argument("--log", type=Path, required=True)
    parser.add_argument("--mirror", type=Path, required=True)
    parser.add_argument("--reprice", action="store_true")
    args = parser.parse_args()
    source = ROOT / f"results/2574_second_chord_grid_{args.cells}.json"
    payload = json.loads(source.read_text())
    deterministic_reprice = False
    if args.reprice:
        subprocess.run([sys.executable, str(ROOT / "scripts/price_second_chord_grid_2574.py"),
                        "--cells", str(args.cells)], check=True, cwd=ROOT)
        repeated = json.loads(source.read_text())
        assert {key: value for key, value in payload.items() if key != "elapsed_seconds"} == {
            key: value for key, value in repeated.items() if key != "elapsed_seconds"}
        payload = repeated
        deterministic_reprice = True
    validate_payload(payload)
    result = dict(record=2574, status="SECOND_CHORD_METHOD_VALIDATED",
                  cells=args.cells, analytic_grid_fits=payload["analytic_grid_fits"],
                  deterministic_non_timing_fields=deterministic_reprice,
                  controls=controls.independent_controls(),
                  endpoint_controls=endpoint_controls(),
                  mutation_rejections=mutation_controls(payload),
                  build=check_build(args.log, args.mirror),
                  source_artifact_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                  validator_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  generic_lean_method_proved=True,
                  **{key: False for key in FALSE_FLAGS})
    out = ROOT / f"results/2574_second_chord_controls_{args.cells}.json"
    out.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps(result), flush=True)


if __name__ == "__main__":
    main()
