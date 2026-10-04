"""Independent arithmetic, owner, mutation, replay and audit gates for fresh nodes."""
import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

import generate_node_exp_owner_2577 as generation
from generate_correction_pair_2570 import rename
from generate_shared_second_chord_2576 import declarations
from generate_signed_cells_2558 import scalar_layout
from validate_adaptive_nodes_2542 import scalar_def
from validate_boundary_jets_2548 import check as check_jet
from validate_compact_replay_2542 import value
from validate_second_chord_cell_2575 import replace_literal, signed_reader

ROOT, DEV = generation.ROOT, generation.DEV


def read(module):
    return (DEV / (module + ".lean")).read_text()


def check_node(index, sign, owner=None, derivatives=None, orders=(2, 3)):
    assert 2 in orders and len(set(orders)) == len(orders) and set(orders) <= {2, 3}
    parent = generation.names(index, sign)
    owner = read(parent["module"]) if owner is None else owner
    derivatives = {} if derivatives is None else derivatives
    parent_fields = declarations(owner)
    expected_position = -Q(65536001, 10**7) + index * Q(65536001, 51200000000)
    assert scalar_def(owner, parent["point"] + "Position2577") == expected_position
    assert "Factor2577" not in owner and "DerivativeError2577" not in owner
    assert "NodeJet" not in owner and "KernelN" not in owner
    sigma = "(-1/2)" if sign < 0 else "(1/2)"
    opposite = "(1/2)" if sign < 0 else "(-1/2)"
    assert sigma in owner and opposite not in owner.replace(sigma, "SIGMA")
    reports = []
    for order in orders:
        child = generation.names(index, sign, order)
        raw = derivatives.get(order, read(child["module"]))
        fields = declarations(raw)
        assert f"import ConnesWeilRH.Dev.{parent['module']}" in raw
        assert "compactExp2547" not in raw and "decide +kernel" not in raw
        assert scalar_def(raw, child["point"] + "Position2577") == expected_position
        assert sigma in raw and opposite not in raw.replace(sigma, "SIGMA")
        restored = raw
        for family in range(30):
            prefix = child["point"] + f"P{family:03d}"
            upstream = parent["point"] + f"P{family:03d}"
            for suffix in ("Input", "Center", "Error"):
                key = prefix + suffix + "2577"
                if key in fields:
                    parser = scalar_def if suffix == "Error" else value
                    assert parser(raw, key) == parser(owner, upstream + suffix + "2577")
            for suffix in ("Exterior", "BaseError"):
                key = prefix + suffix + "2577"
                if key in fields:
                    argument = " n" if suffix == "Exterior" else ""
                    assert re.search(r"exact\s+" + upstream + suffix + r"2577" + argument + r"\s*$",
                                     fields[key])
                    inherited = rename(parent_fields[upstream + suffix + "2577"], parent["point"],
                                       2577, child["point"], 2577)
                    restored = restored.replace(fields[key].strip(), inherited.strip())
        restored = scalar_layout(rename(restored, child["point"], 2577, "edgeMidpoint", 2548))
        report = check_jet(restored, "Midpoint", grid_order=(Q(index), order), sigma=Q(sign, 2))
        _, standalone, active = generation.standalone(index, sign, order)
        standalone_fields = declarations(standalone)
        for family in range(30):
            key = child["point"] + f"P{family:03d}DerivativeError2577"
            normalize = lambda text: re.sub(r"\s+", " ", text).strip()
            assert normalize(fields[key]) == normalize(standalone_fields[key])
        assert report["active"] == active
        reports.append(report)
    child = generation.names(index, sign, 2)
    bounds = read(child["bounds"])
    base = scalar_layout(rename(read(child["module"]), child["point"], 2577, "midpoint", 2543))
    signed = scalar_layout(rename(bounds, child["point"], 2577, "midpoint", 2543))
    signed = rename(signed, child["signed"], 2577, "signedMidpoint", 2543)
    assert "baseCoefficient" not in signed
    reading = signed_reader()(signed, base)
    return dict(index=index, sign=sign, orders=reports, second_upper=reading["signed_upper"],
                rounding_charge=reading["evaluation_charge"])


def rejected(label, action):
    try:
        action()
    except AssertionError:
        return label
    raise AssertionError("mutation accepted: " + label)


def controls(payload):
    assert payload["record"] == 2577 and payload["signs"] == [-1, 1]
    assert payload["orders"] == [2, 3]
    assert payload["coefficient_owner"] == "ideal_correction_coefficient"
    assert Q(payload["error"]) == Q(1, 10**28)
    for key in ("full_grid_certificate", "exact_coefficient_membership", "producer_go", "rh_claim"):
        assert payload[key] is False
    for relative, expected in {**payload["input_sha256"], **payload["output_sha256"]}.items():
        path = ROOT / relative
        assert path.resolve().is_relative_to(ROOT.resolve())
        assert hashlib.sha256(path.read_bytes()).hexdigest() == expected, relative
    readings, mutations = [], []
    for row in payload["rows"]:
        index, sign = row["index"], row["sign"]
        reading = check_node(index, sign)
        assert Q(reading["second_upper"]) == Q(row["second_upper"])
        assert Q(reading["rounding_charge"]) == Q(row["rounding_charge"])
        assert all(order["active"] == row["active"] for order in reading["orders"])
        readings.append(reading)
        active = row["active"]
        assert active
        family = active[0]
        child = generation.names(index, sign, 2)
        parent = generation.names(index, sign)
        raw = read(child["module"])
        third = read(generation.names(index, sign, 3)["module"])
        prefix = child["point"] + f"P{family:03d}"
        factor3 = value(third, generation.names(index, sign, 3)["point"] + f"P{family:03d}Factor2577")
        from generate_compact_replay_2542 import pair
        changed_factor = replace_literal(raw, prefix + "Factor2577", pair(factor3))
        changed_owner = raw.replace(parent["point"] + f"P{family:03d}BaseError2577",
                                    generation.names(index, -sign)["point"] + f"P{family:03d}BaseError2577")
        sigma = "(-1/2)" if sign < 0 else "(1/2)"
        changed_sign = raw.replace(sigma, "(1/2)" if sign < 0 else "(-1/2)")
        changed_position = replace_literal(read(parent["module"]), parent["point"] + "Position2577", "0")
        for label, source in (("factor", changed_factor), ("owner", changed_owner), ("sign", changed_sign)):
            assert source != raw
            mutations.append(rejected(f"{label}_{index}_{sign}",
                                      lambda source=source: check_node(index, sign, derivatives={2: source})))
        mutations.append(rejected(f"position_{index}_{sign}",
                                  lambda: check_node(index, sign, owner=changed_position)))
    return readings, mutations


def build_controls(payload, log_path, mirror):
    log = log_path.read_text()
    assert "Build completed successfully" in log
    assert not re.search(r"^error:|\bsorry(?:Ax)?\b", log, re.MULTILINE)
    observed = dict(re.findall(r"'ConnesWeilRH\.Dev\.(\w+)' depends on axioms:\s*\[([^]]*)\]", log))
    expected = payload["audit_targets"]
    assert len(expected) == 158 * len(payload["rows"]) and len(set(expected)) == len(expected)
    for target in expected:
        assert [part.strip() for part in observed.get(target, "").split(",")] == [
            "propext", "Classical.choice", "Quot.sound"], target
    pending = ["ConnesWeilRH"] + ["ConnesWeilRH.Dev." + module for module in payload["modules"]]
    hashes = {}
    while pending:
        relative = pending.pop().replace(".", "/") + ".lean"
        if relative in hashes:
            continue
        data = (ROOT / relative).read_bytes()
        assert data == (mirror / relative).read_bytes(), relative
        hashes[relative] = hashlib.sha256(data).hexdigest()
        for line in data.decode("utf-8-sig").splitlines():
            if line.startswith("import "):
                pending.extend(module for module in line[7:].split() if module.startswith("ConnesWeilRH"))
    for relative in ("lean-toolchain", "lake-manifest.json", "lakefile.toml"):
        data = (ROOT / relative).read_bytes()
        assert data == (mirror / relative).read_bytes()
        hashes[relative] = hashlib.sha256(data).hexdigest()
    return dict(verified_targets=len(expected), axiom_trio=True, mirror_files=len(hashes),
                source_sha256=hashes, log_sha256=hashlib.sha256(log_path.read_bytes()).hexdigest())


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--log", type=Path, required=True)
    parser.add_argument("--mirror", type=Path, required=True)
    args = parser.parse_args()
    artifact = ROOT / "results/2577_node_exp_generation.json"
    payload = json.loads(artifact.read_text())
    readings, mutations = controls(payload)
    before = {path: (ROOT / path).read_bytes() for path in payload["output_sha256"]}
    artifact_bytes = artifact.read_bytes()
    subprocess.run([sys.executable, str(ROOT / "scripts/generate_node_exp_owner_2577.py"),
                    "--indices", *map(str, payload["indices"])], check=True, stdout=subprocess.DEVNULL)
    assert artifact.read_bytes() == artifact_bytes
    assert all((ROOT / path).read_bytes() == data for path, data in before.items())
    result = dict(record=2577, status="NODE_EXP_OWNER_VALIDATED", readings=readings,
                  mutation_rejections=mutations, deterministic_regeneration=True,
                  build=build_controls(payload, args.log, args.mirror),
                  validator_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  full_grid_certificate=False, exact_coefficient_membership=False,
                  producer_go=False, rh_claim=False)
    output = ROOT / "results/2577_node_exp_validation.json"
    output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8", newline="\n")
    print("NODE_EXP_OWNER_VALIDATED", len(readings), len(mutations), result["build"]["verified_targets"], flush=True)


if __name__ == "__main__":
    main()
