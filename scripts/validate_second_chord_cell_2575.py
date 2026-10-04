"""Independent payload replay and kernel-audit gates for second-chord cell 2575."""
import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

from flint import ctx
import generate_second_chord_cell_2575 as generation
from generate_correction_pair_2570 import CENTER_SWAPS, derive_generator, rename
from generate_signed_cells_2558 import scalar_layout
from validate_adaptive_nodes_2542 import scalar_def
from validate_boundary_jets_2548 import check as check_jet
from validate_boundary_fourth_2550 import check as check_fourth
import price_second_chord_grid_2574 as pricing

ROOT = generation.ROOT
DEV = generation.DEV


def endpoint_sources(index, sign):
    names = generation.point_names(index, sign)
    raw = (DEV / (names["deriv"] + ".lean")).read_text()
    bounds = (DEV / (names["bounds"] + ".lean")).read_text()
    assert "baseCoefficient" not in bounds
    raw = scalar_layout(rename(raw, names["point"], 2575, "edgeMidpoint", 2548))
    base = scalar_layout(rename(raw, "edgeMidpoint", 2548, "midpoint", 2543))
    bounds = scalar_layout(rename(bounds, names["point"], 2575, "midpoint", 2543))
    bounds = rename(bounds, names["signed"], 2575, "signedMidpoint", 2543)
    return raw, base, bounds


def signed_reader():
    derived = derive_generator(ROOT / "scripts/validate_midpoint_derivatives_2543.py",
                               CENTER_SWAPS + [("Q(30,10**30)", "Q(30,10**28)")])
    return derived["check_signed"]


def reject(name, action):
    try:
        action()
    except AssertionError:
        return name
    raise AssertionError("corrupted artifact accepted: " + name)


def replace_literal(source, name, literal):
    pattern = r"((?:noncomputable )?def " + re.escape(name) + r"\b.*?:=).*?(?=\n\n(?:def|noncomputable def|theorem))"
    changed, count = re.subn(pattern, lambda match: match[1] + " " + literal,
                            source, count=1, flags=re.DOTALL)
    assert count == 1 and changed != source
    return changed


def payload_controls(payload):
    assert payload["record"] == 2575 and payload["cell"] == 2700
    assert payload["coefficient_owner"] == "ideal_correction_coefficient"
    assert payload["generator_sha256"] == hashlib.sha256(
        (ROOT / "scripts/generate_second_chord_cell_2575.py").read_bytes()).hexdigest()
    for relative, expected in payload["input_sha256"].items():
        path = ROOT / relative
        assert path.resolve().is_relative_to(ROOT.resolve())
        assert hashlib.sha256(path.read_bytes()).hexdigest() == expected
    assert Q(payload["error"]) == generation.ERROR
    for key in ("full_grid_certificate", "exact_coefficient_membership", "producer_go", "rh_claim"):
        assert payload[key] is False
    assert [(row["index"], row["sign"]) for row in payload["endpoint_rows"]] == [
        (2700, -1), (2701, -1), (2700, 1), (2701, 1)]
    assert [row["sign"] for row in payload["cell_rows"]] == [-1, 1]
    ctx.prec = 192
    families = pricing.previous.load_families()
    read_signed = signed_reader()
    endpoints = []
    rejections = []
    for row in payload["endpoint_rows"]:
        index, sign = row["index"], row["sign"]
        raw, base, bounds = endpoint_sources(index, sign)
        reading = check_jet(raw, "Midpoint", grid_order=(Q(index), 2), sigma=Q(sign, 2))
        assert reading["active"] == row["active"]
        signed = read_signed(bounds, base)
        upper = Q(signed["signed_upper"])
        assert Q(signed["evaluation_charge"]) == Q(row["rounding_charge"])
        assert upper == Q(row["upper"])
        assert scalar_def(base, "midpointPosition2543") == Q(row["position"])
        external = pricing.second_point(families, Q(row["position"]), Q(sign, 2))
        assert external <= upper
        endpoints.append(dict(index=index, sign=sign, independent_replay=reading,
                              upper=str(upper), external_point_upper=str(external),
                              rounding_charge=row["rounding_charge"]))
        active = reading["active"][0]
        changed = replace_literal(raw, f"edgeMidpointP{active:03d}Factor2548", "(0, 0)")
        rejections.append(reject(f"zero_factor_{index}_{sign}", lambda:
            check_jet(changed, "Midpoint", grid_order=(Q(index), 2), sigma=Q(sign, 2))))
        changed = replace_literal(bounds, f"midpointP{active:03d}Rounded2543", "(0, 0)")
        rejections.append(reject(f"changed_rounded_{index}_{sign}", lambda:
            read_signed(changed, base)))
        rejections.append(reject(f"opposite_sign_{index}_{sign}", lambda:
            check_jet(raw, "Midpoint", grid_order=(Q(index), 2), sigma=Q(-sign, 2))))
    rows = json.loads((ROOT / "results/2338_exact_interpolation_repair.json").read_text())["coefficient_rows"]
    assembly = (DEV / (generation.ASSEMBLY + ".lean")).read_text()
    cells = []
    for cell in payload["cell_rows"]:
        sign = cell["sign"]
        side = generation.side_name(sign)
        parent = f"batchC02700{side}Fourth"
        fourth_source = (DEV / f"C1RouteABatchC02700{side}Fourth2558.lean").read_text()
        normalized = scalar_layout(rename(fourth_source, parent, 2558, "edgeFourth", 2550))
        assert len(check_fourth(normalized, cell_index=2700, sigma=Q(sign, 2))) == 30
        fourth = Q(0)
        for index, row in enumerate(rows):
            box = row["ideal_correction_coefficient"]
            center = [(Q(box[part]["lower_exact"]) + Q(box[part]["upper_exact"])) / 2
                      for part in ("real", "imag")]
            fourth += (sum(abs(value) for value in center) + generation.ERROR) * scalar_def(
                normalized, f"edgeFourthP{index:03d}Upper2550")
        endpoint_piece = generation.STEP / 2 * sum(Q(row["upper"]) for row in endpoints
                                                 if row["sign"] == sign)
        remainder = generation.STEP ** 3 / 12 * fourth
        assert Q(cell["fourth_upper"]) == fourth
        assert Q(cell["endpoint_piece"]) == endpoint_piece
        assert Q(cell["remainder_piece"]) == remainder
        assert Q(cell["cell_upper"]) == endpoint_piece + remainder
        prefix = f"corrSecondChord{side}2575"
        assert scalar_def(assembly, prefix + "FourthUpper") == fourth
        assert scalar_def(assembly, prefix + "Upper") == endpoint_piece + remainder
        cells.append(dict(sign=sign, exact_upper=cell["cell_upper"],
                          display_upper=float(endpoint_piece + remainder),
                          fourth_payloads=30))
    for relative, expected in payload["source_sha256"].items():
        path = ROOT / relative
        assert path.resolve().is_relative_to(ROOT.resolve())
        assert hashlib.sha256(path.read_bytes()).hexdigest() == expected
    return endpoints, cells, rejections


def build_controls(payload, log_path, mirror):
    log = log_path.read_text()
    assert "Build completed successfully" in log
    assert not re.search(r"^error:|\bsorry(?:Ax)?\b", log, re.MULTILINE)
    readings = dict(re.findall(r"'ConnesWeilRH\.Dev\.(\w+)' depends on axioms:\s*\[([^]]*)\]", log))
    expected = payload["audit_targets"]
    assert len(expected) == 154 and len(set(expected)) == 154
    for name in expected:
        assert [part.strip() for part in readings.get(name, "").split(",")] == [
            "propext", "Classical.choice", "Quot.sound"], name
    pending = ["ConnesWeilRH"] + ["ConnesWeilRH.Dev." + module for module in payload["modules"]]
    hashes = {}
    while pending:
        relative = pending.pop().replace(".", "/") + ".lean"
        if relative in hashes:
            continue
        path = ROOT / relative
        data = path.read_bytes()
        assert data == (mirror / relative).read_bytes(), relative
        hashes[relative] = hashlib.sha256(data).hexdigest()
        for line in data.decode("utf-8-sig").splitlines():
            if line.startswith("import "):
                pending.extend(module for module in line[7:].split()
                               if module.startswith("ConnesWeilRH"))
    for relative in ("lean-toolchain", "lake-manifest.json", "lakefile.toml"):
        data = (ROOT / relative).read_bytes()
        assert data == (mirror / relative).read_bytes(), relative
        hashes[relative] = hashlib.sha256(data).hexdigest()
    return dict(verified_targets=len(expected), axiom_trio=True,
                mirror_files=len(hashes), source_sha256=hashes,
                log_sha256=hashlib.sha256(log_path.read_bytes()).hexdigest())


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--log", type=Path, required=True)
    parser.add_argument("--mirror", type=Path, required=True)
    args = parser.parse_args()
    path = ROOT / "results/2575_second_chord_generation.json"
    payload = json.loads(path.read_text())
    endpoints, cells, rejected = payload_controls(payload)
    before = {relative: (ROOT / relative).read_bytes() for relative in payload["source_sha256"]}
    artifact_before = path.read_bytes()
    subprocess.run([sys.executable, str(ROOT / "scripts/generate_second_chord_cell_2575.py")],
                   check=True, cwd=ROOT, stdout=subprocess.DEVNULL)
    assert artifact_before == path.read_bytes()
    assert all(data == (ROOT / relative).read_bytes() for relative, data in before.items())
    result = dict(record=2575, status="SECOND_CHORD_CELL_KERNEL_VALIDATED",
                  cell=2700, endpoint_controls=endpoints, cell_controls=cells,
                  mutation_rejections=rejected, deterministic_regeneration=True,
                  regression_modules=payload["regression_modules"],
                  build=build_controls(payload, args.log, args.mirror),
                  generator_sha256=hashlib.sha256((ROOT / "scripts/generate_second_chord_cell_2575.py").read_bytes()).hexdigest(),
                  validator_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  cell_second_integral_certificate=True, full_grid_certificate=False,
                  exact_coefficient_membership=False, producer_go=False, rh_claim=False)
    output = ROOT / "results/2575_second_chord_validation.json"
    output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps({key: value for key, value in result.items() if key != "build"}), flush=True)
    print("AXIOM_TARGETS", result["build"]["verified_targets"],
          "MIRROR_FILES", result["build"]["mirror_files"], flush=True)


if __name__ == "__main__":
    main()
