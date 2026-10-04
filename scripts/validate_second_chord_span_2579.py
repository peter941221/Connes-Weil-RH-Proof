"""Independent arithmetic, mutation, regeneration and Lean audit gates for 2579."""
import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

import generate_second_chord_span_2579 as generation
from generate_correction_pair_2570 import rename
from generate_compact_replay_2542 import pair
from generate_signed_cells_2558 import scalar_layout
from validate_adaptive_nodes_2542 import scalar_def
from validate_boundary_fourth_2550 import check as check_fourth
from validate_node_exp_owner_2577 import check_node, rejected
from validate_compact_replay_2542 import value
from validate_second_chord_cell_2575 import replace_literal

ROOT, DEV = generation.ROOT, generation.DEV


def read(module):
    return (DEV / (module + ".lean")).read_text(encoding="utf-8")


def verify_total(source, sign, fourth, total):
    prefix = f"nodeSecondChord{generation.side_name(sign)}2579"
    assert scalar_def(source, prefix + "FourthUpper") == fourth
    assert scalar_def(source, prefix + "Upper") == total


def build_controls(log_path, mirror, targets):
    log = log_path.read_text(encoding="utf-8")
    assert "Build completed successfully" in log
    assert not re.search(r"^error:|sorryAx", log, re.MULTILINE)
    observed = dict(re.findall(r"'ConnesWeilRH\.Dev\.(\w+)' depends on axioms:\s*\[([^]]*)\]", log))
    assert len(targets) == len(set(targets))
    for target in targets:
        assert [part.strip() for part in observed.get(target, "").split(",")] == [
            "propext", "Classical.choice", "Quot.sound"], target
    pending, hashes = ["ConnesWeilRH.Dev." + generation.AUDIT], {}
    while pending:
        module = pending.pop()
        relative = module.replace(".", "/") + ".lean"
        if relative in hashes:
            continue
        data = (ROOT / relative).read_bytes()
        assert data == (mirror / relative).read_bytes(), relative
        hashes[relative] = hashlib.sha256(data).hexdigest()
        for line in data.decode("utf-8-sig").splitlines():
            if line.startswith("import "):
                pending.extend(name for name in line[7:].split() if name.startswith("ConnesWeilRH"))
    for relative in ("lean-toolchain", "lake-manifest.json", "lakefile.toml"):
        data = (ROOT / relative).read_bytes()
        assert data == (mirror / relative).read_bytes(), relative
        hashes[relative] = hashlib.sha256(data).hexdigest()
    return dict(verified_targets=len(targets), axiom_trio=True, mirror_files=len(hashes),
                source_sha256=hashes, log_sha256=hashlib.sha256(log_path.read_bytes()).hexdigest())


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--log", type=Path, required=True)
    parser.add_argument("--mirror", type=Path, required=True)
    args = parser.parse_args()
    generation_path = ROOT / "results/2579_second_chord_generation.json"
    generation_before = generation_path.read_bytes()
    payload = json.loads(generation_before)
    assert payload["generated_orders"] == [2] and payload["new_node"] == 2704
    assert not any("NodeJet3" in relative for relative in payload["output_sha256"])
    for relative, digest in payload["input_sha256"].items():
        assert hashlib.sha256((ROOT / relative).read_bytes()).hexdigest() == digest, relative
    paths = list(payload["output_sha256"])
    before = {relative: (ROOT / relative).read_bytes() for relative in paths}
    for relative, digest in payload["output_sha256"].items():
        assert hashlib.sha256(before[relative]).hexdigest() == digest, relative
    for field in ("full_grid_certificate", "exact_coefficient_membership", "producer_go", "rh_claim"):
        assert payload[field] is False
    endpoints, cells, mutations = [], [], []
    mutations.append(rejected("empty_orders", lambda: check_node(2703, -1, orders=())))
    mutations.append(rejected("unsupported_orders", lambda: check_node(2703, -1, orders=(2, 4))))
    assembly = read(generation.ASSEMBLY)
    coefficient_rows = json.loads((ROOT / "results/2338_exact_interpolation_repair.json").read_text())["coefficient_rows"]
    for sign in (-1, 1):
        for index in (2703, 2704):
            row = check_node(index, sign, orders=(2,))
            endpoints.append(row)
            naming = generation.owner.names(index, sign, 2)
            parent = generation.owner.names(index, sign)
            raw = read(naming["module"])
            family = row["orders"][0]["active"][0]
            changed = replace_literal(raw, naming["point"] + f"P{family:03d}Factor2577", "(0, 0)")
            mutations.append(rejected(f"zero_factor_{index}_{sign}", lambda:
                check_node(index, sign, derivatives={2: changed}, orders=(2,))))
            third_names, third_source, _ = generation.owner.standalone(index, sign, 3)
            factor = value(third_source, third_names["point"] + f"P{family:03d}Factor2577")
            changed = replace_literal(raw, naming["point"] + f"P{family:03d}Factor2577", pair(factor))
            mutations.append(rejected(f"wrong_derivative_order_{index}_{sign}", lambda:
                check_node(index, sign, derivatives={2: changed}, orders=(2,))))
            changed = raw.replace(parent["point"] + f"P{family:03d}BaseError2577",
                                  generation.owner.names(index, -sign)["point"] + f"P{family:03d}BaseError2577")
            assert changed != raw
            mutations.append(rejected(f"opposite_owner_{index}_{sign}", lambda:
                check_node(index, sign, derivatives={2: changed}, orders=(2,))))
            changed = replace_literal(read(parent["module"]), parent["point"] + "Position2577", "0")
            mutations.append(rejected(f"wrong_position_{index}_{sign}", lambda:
                check_node(index, sign, owner=changed, orders=(2,))))
        legacy = check_node(2703, sign)
        assert [row["order"] for row in legacy["orders"]] == [2, 3]
        assert Q(legacy["second_upper"]) == Q(next(row["second_upper"] for row in endpoints
                                                  if row["index"] == 2703 and row["sign"] == sign))
        side = generation.side_name(sign)
        prefix = f"batchC02703{side}Fourth"
        normalized = scalar_layout(rename(read(generation.fourth_module(sign)), prefix, 2558, "edgeFourth", 2550))
        reports = check_fourth(normalized, cell_index=2703, sigma=Q(sign, 2))
        assert len(reports) == 30
        fourth = Q(0)
        for index, coefficient in enumerate(coefficient_rows):
            box = coefficient["ideal_correction_coefficient"]
            center = [(Q(box[part]["lower_exact"]) + Q(box[part]["upper_exact"])) / 2 for part in ("real", "imag")]
            fourth += (sum(abs(value) for value in center) + Q(1, 10**28)) * scalar_def(normalized, f"edgeFourthP{index:03d}Upper2550")
        matching = [row for row in endpoints if row["sign"] == sign]
        endpoint_piece = generation.STEP / 2 * sum(Q(row["second_upper"]) for row in matching)
        remainder = fourth * generation.STEP**3 / 12
        total = endpoint_piece + remainder
        verify_total(assembly, sign, fourth, total)
        previous = scalar_def(read("C1RouteACorrectionSecondChordCell2702_2578"), f"nodeSecondChord{side}2578Upper")
        cells.append(dict(sign=sign, endpoint_piece=str(endpoint_piece), remainder_piece=str(remainder),
                          fourth_upper=str(fourth), cell_upper=str(total), display_upper=float(total),
                          span_upper=str(previous + total), display_span_upper=float(previous + total)))
        family = next(row["family"] for row in reports if not row["exterior"])
        changed = replace_literal(normalized, f"edgeFourthP{family:03d}Upper2550", "0")
        mutations.append(rejected(f"zero_fourth_{sign}", lambda:
            check_fourth(changed, cell_index=2703, sigma=Q(sign, 2))))
        mutations.append(rejected(f"wrong_fourth_sign_{sign}", lambda:
            check_fourth(normalized, cell_index=2703, sigma=Q(-sign, 2))))
        changed = generation.replace_definition(assembly, f"nodeSecondChord{side}2579Upper", Q(0))
        mutations.append(rejected(f"zero_cell_total_{sign}", lambda: verify_total(changed, sign, fourth, total)))
    subprocess.run([sys.executable, str(ROOT / "scripts/generate_second_chord_span_2579.py")], check=True)
    assert all((ROOT / relative).read_bytes() == data for relative, data in before.items())
    assert generation_path.read_bytes() == generation_before
    audit_targets = re.findall(r"#print axioms ConnesWeilRH\.Dev\.(\w+)", read(generation.AUDIT))
    assert audit_targets == payload["audit_targets"]
    result = dict(record=2579, status="SECOND_CHORD_SPAN_VALIDATED", cell=2703, span_cells=[2702, 2703],
                  endpoints=endpoints, cells=cells, mutation_controls=mutations, deterministic_regeneration=True,
                  legacy_default_orders_verified=True,
                  build=build_controls(args.log, args.mirror, audit_targets),
                  full_grid_certificate=False, exact_coefficient_membership=False, producer_go=False, rh_claim=False)
    result["validator_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    result["input_sha256"] = payload["input_sha256"]
    (ROOT / "results/2579_second_chord_validation.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8", newline="\n")
    print("SECOND_CHORD_SPAN_VALIDATED", len(endpoints), len(mutations), result["build"]["verified_targets"], flush=True)


if __name__ == "__main__":
    main()
