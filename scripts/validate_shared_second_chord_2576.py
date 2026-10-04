"""Independent constant/owner replay, axiom audit and same-run compiler timing."""
import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import re
import statistics
import subprocess
import sys
import tempfile
import time

import generate_shared_second_chord_2576 as generation
import generate_second_chord_cell_2575 as prior
from generate_correction_pair_2570 import rename
from generate_signed_cells_2558 import scalar_layout
from validate_adaptive_nodes_2542 import scalar_def
from validate_compact_replay_2542 import value
from validate_boundary_jets_2548 import check as check_jet
from validate_second_chord_cell_2575 import signed_reader

ROOT = generation.ROOT
DEV = generation.DEV


def compact(source):
    return re.sub(r"\s+", "", source)


def check_shared_source(index, sign, source):
    old = prior.point_names(index, sign)
    new = generation.names(index, sign)
    baseline = (DEV / (old["deriv"] + ".lean")).read_text()
    kernel = (DEV / (new["kernel_module"] + ".lean")).read_text()
    blocks = generation.declarations(source)
    assert "compactExp2547" not in source and "decide +kernel" not in source
    sigma = "(-1/2)" if sign < 0 else "(1/2)"
    assert sigma in source
    assert ("(1/2)" if sign < 0 else "(-1/2)") not in source.replace(sigma, "SIGMA")
    assert scalar_def(source, new["point"] + "Position2576") == scalar_def(
        kernel, new["kernel"] + "Position2555")
    old_blocks = generation.declarations(baseline)
    active = []
    for family in range(30):
        new_family = new["point"] + f"P{family:03d}"
        old_family = old["point"] + f"P{family:03d}"
        kernel_family = new["kernel"] + f"P{family:03d}"
        for suffix in ("Center", "Error"):
            read = value if suffix == "Center" else scalar_def
            assert read(source, new_family + suffix + "2576") == read(
                kernel, kernel_family + suffix + "2555")
        assert value(source, new_family + "Factor2576") == value(
            baseline, old_family + "Factor2575")
        body = blocks[new_family + "BaseError2576"]
        proof_start = re.search(r":=\s*by\b", body)
        assert proof_start
        assert compact(body[proof_start.start():]) == compact(
            ":= by exact " + kernel_family + "BaseError2555")
        derivative = rename(blocks[new_family + "DerivativeError2576"],
                            new["point"], 2576, old["point"], 2575)
        assert compact(derivative) == compact(old_blocks[old_family + "DerivativeError2575"])
        if new_family + "Input2576" in blocks:
            active.append(family)
            assert value(source, new_family + "Input2576") == value(
                kernel, kernel_family + "Input2555")
            assert value(source, new_family + "Factor2576") != value(
                kernel, kernel_family + "Factor2555")
    return active


def controls(payload):
    assert payload["record"] == 2576 and payload["cell"] == 2700
    assert payload["exponentials_recomputed"] == 0
    for key in ("full_grid_certificate", "exact_coefficient_membership", "producer_go", "rh_claim"):
        assert payload[key] is False
    predecessor = json.loads((ROOT / "results/2575_second_chord_generation.json").read_text())
    assert payload["endpoint_rows"] == predecessor["endpoint_rows"]
    assert payload["cell_rows"] == predecessor["cell_rows"]
    reports = []
    rejected = []
    read_signed = signed_reader()
    for reading in payload["controls"]:
        index, sign = reading["index"], reading["sign"]
        old = prior.point_names(index, sign)
        new = generation.names(index, sign)
        raw = (DEV / (new["deriv"] + ".lean")).read_text()
        kernel = (DEV / (new["kernel_module"] + ".lean")).read_text()
        active = check_shared_source(index, sign, raw)
        assert active == reading["active"]
        kernel_normalized = scalar_layout(rename(kernel, new["kernel"], 2555, "edgeMidpoint", 2548))
        kernel_reading = check_jet(kernel_normalized, "Midpoint", grid_order=(Q(index), 3), sigma=Q(sign, 2))
        old_source = (DEV / (old["deriv"] + ".lean")).read_text()
        old_normalized = scalar_layout(rename(old_source, old["point"], 2575, "edgeMidpoint", 2548))
        old_reading = check_jet(old_normalized, "Midpoint", grid_order=(Q(index), 2), sigma=Q(sign, 2))
        assert kernel_reading["active"] == old_reading["active"] == active
        bounds = (DEV / (new["bounds"] + ".lean")).read_text()
        restored = rename(bounds, new["point"], 2576, old["point"], 2575)
        restored = rename(restored, new["signed"], 2576, old["signed"], 2575)
        restored = restored.replace(new["prefix"] + "Physical2576", old["prefix"] + "Physical2575")
        restored = restored.replace(new["deriv"], old["deriv"])
        assert compact(restored) == compact((DEV / (old["bounds"] + ".lean")).read_text())
        normalized_bounds = scalar_layout(rename(bounds, new["point"], 2576, "midpoint", 2543))
        normalized_bounds = rename(normalized_bounds, new["signed"], 2576, "signedMidpoint", 2543)
        normalized_raw = scalar_layout(rename(raw, new["point"], 2576, "midpoint", 2543))
        signed = read_signed(normalized_bounds, normalized_raw)
        expected = next(row for row in predecessor["endpoint_rows"]
                        if row["index"] == index and row["sign"] == sign)
        assert Q(signed["signed_upper"]) == Q(expected["upper"])
        family = active[0]
        factor_name = new["point"] + f"P{family:03d}Factor2576"
        fields = generation.declarations(raw)
        wrong_factor = generation.declarations(kernel)[new["kernel"] + f"P{family:03d}Factor2555"]
        wrong_factor = wrong_factor.replace(new["kernel"] + f"P{family:03d}Factor2555", factor_name)
        changed_factor = raw.replace(fields[factor_name], wrong_factor)
        wrong_owner = raw.replace(new["kernel"] + f"P{family:03d}BaseError2555",
                                 generation.names(2701 if index == 2700 else 2700, sign)["kernel"] +
                                 f"P{family:03d}BaseError2555")
        wrong_sign = raw.replace(sigma := ("(-1/2)" if sign < 0 else "(1/2)"),
                                 "(1/2)" if sign < 0 else "(-1/2)")
        for label, changed in (("third_factor", changed_factor), ("wrong_owner", wrong_owner),
                               ("wrong_sign", wrong_sign)):
            assert changed != raw
            try:
                check_shared_source(index, sign, changed)
            except AssertionError:
                rejected.append(f"{label}_{index}_{sign}")
            else:
                raise AssertionError("mutation accepted: " + label)
        reports.append(dict(index=index, sign=sign, active=active,
                            signed_upper=signed["signed_upper"],
                            active_exponentials_reused=len(active)))
    assembly = (DEV / (generation.ASSEMBLY + ".lean")).read_text()
    for row in predecessor["cell_rows"]:
        prefix = f"sharedSecondChord{prior.side_name(row['sign'])}2576"
        assert scalar_def(assembly, prefix + "Upper") == Q(row["cell_upper"])
        assert scalar_def(assembly, prefix + "FourthUpper") == Q(row["fourth_upper"])
    for relative, expected in {**payload["input_sha256"], **payload["output_sha256"]}.items():
        path = ROOT / relative
        assert path.resolve().is_relative_to(ROOT.resolve())
        assert hashlib.sha256(path.read_bytes()).hexdigest() == expected, relative
    return reports, rejected


def build_controls(payload, log_path, mirror):
    log = log_path.read_text()
    assert "Build completed successfully" in log
    assert not re.search(r"^error:|\bsorry(?:Ax)?\b", log, re.MULTILINE)
    observed = dict(re.findall(r"'ConnesWeilRH\.Dev\.(\w+)' depends on axioms:\s*\[([^]]*)\]", log))
    expected = payload["audit_targets"]
    assert len(expected) == 274 and len(set(expected)) == 274
    for name in expected:
        assert [part.strip() for part in observed.get(name, "").split(",")] == [
            "propext", "Classical.choice", "Quot.sound"], name
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


def timing(lake, mirror, repetitions):
    import resource

    assert repetitions >= 2
    samples = {}
    usage_samples = {}
    warmup_samples = []
    with tempfile.TemporaryDirectory(prefix="rh_shared_exp_") as temp:
        paths = {}
        for sign in (-1, 1):
            for index in (2700, 2701):
                for label, owner in (("standalone", prior.point_names(index, sign)),
                                      ("shared", generation.names(index, sign))):
                    source = (DEV / (owner["deriv"] + ".lean")).read_text()
                    source = re.sub(r"^#print axioms.*\n?", "", source, flags=re.MULTILINE)
                    path = Path(temp) / f"{label}_{index}_{sign}.lean"
                    path.write_text(source, encoding="utf-8", newline="\n")
                    paths[index, sign, label] = path
                    samples[index, sign, label] = []
                    usage_samples[index, sign, label] = []
        for sign in (-1, 1):
            for index in (2700, 2701):
                for label in ("standalone", "shared"):
                    started = time.monotonic()
                    completed = subprocess.run([str(lake), "env", "lean", str(paths[index, sign, label])],
                                               cwd=mirror, capture_output=True, text=True)
                    elapsed = time.monotonic() - started
                    assert completed.returncode == 0, completed.stdout + completed.stderr
                    assert not re.search(r"\berror:|\bsorry(?:Ax)?\b", completed.stdout + completed.stderr)
                    warmup_samples.append(dict(index=index, sign=sign, label=label, seconds=elapsed))
                    print("COMPILE_WARMUP", index, sign, label, elapsed, flush=True)
        for repetition in range(repetitions):
            labels = ("standalone", "shared") if repetition % 2 == 0 else ("shared", "standalone")
            for sign in (-1, 1):
                for index in (2700, 2701):
                    for label in labels:
                        started = time.monotonic()
                        usage_before = resource.getrusage(resource.RUSAGE_CHILDREN)
                        completed = subprocess.run([str(lake), "env", "lean", str(paths[index, sign, label])],
                                                   cwd=mirror, capture_output=True, text=True)
                        elapsed = time.monotonic() - started
                        usage_after = resource.getrusage(resource.RUSAGE_CHILDREN)
                        assert completed.returncode == 0, completed.stdout + completed.stderr
                        assert not re.search(r"\berror:|\bsorry(?:Ax)?\b", completed.stdout + completed.stderr)
                        samples[index, sign, label].append(elapsed)
                        usage_samples[index, sign, label].append(dict(
                            user_seconds=usage_after.ru_utime - usage_before.ru_utime,
                            system_seconds=usage_after.ru_stime - usage_before.ru_stime,
                            minor_faults=usage_after.ru_minflt - usage_before.ru_minflt,
                            major_faults=usage_after.ru_majflt - usage_before.ru_majflt))
                        print("COMPILE_TIMING", repetition, index, sign, label, elapsed, flush=True)
    rows = []
    for sign in (-1, 1):
        for index in (2700, 2701):
            old = samples[index, sign, "standalone"]
            new = samples[index, sign, "shared"]
            before, after = statistics.mean(old), statistics.mean(new)
            rows.append(dict(index=index, sign=sign, before_seconds=before, after_seconds=after,
                             delta_percent=100 * (after / before - 1),
                             standalone_samples=old, shared_samples=new,
                             standalone_usage=usage_samples[index, sign, "standalone"],
                             shared_usage=usage_samples[index, sign, "shared"]))
    return dict(repetitions=repetitions, rows=rows, imports_warm=True,
                axiom_prints_removed_from_both=True, alternating_order=True,
                warmup_samples=warmup_samples, warmup_rounds=1,
                scope="fixed-input compiler runs; not new grid cells or full-grid timing")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--log", type=Path, required=True)
    parser.add_argument("--mirror", type=Path, required=True)
    parser.add_argument("--lake", type=Path)
    parser.add_argument("--repetitions", type=int, default=2)
    args = parser.parse_args()
    artifact = ROOT / "results/2576_shared_exp_generation.json"
    payload = json.loads(artifact.read_text())
    reports, rejected = controls(payload)
    before = {relative: (ROOT / relative).read_bytes() for relative in payload["output_sha256"]}
    original_artifact = artifact.read_bytes()
    subprocess.run([sys.executable, str(ROOT / "scripts/generate_shared_second_chord_2576.py")],
                   check=True, cwd=ROOT, stdout=subprocess.DEVNULL)
    assert artifact.read_bytes() == original_artifact
    assert all((ROOT / relative).read_bytes() == data for relative, data in before.items())
    result = dict(record=2576, status="SHARED_EXP_SECOND_CHORD_VALIDATED", controls=reports,
                  mutation_rejections=rejected, deterministic_regeneration=True,
                  cell_rows=payload["cell_rows"], build=build_controls(payload, args.log, args.mirror),
                  timing=timing(args.lake, args.mirror, args.repetitions) if args.lake else None,
                  validator_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  full_grid_certificate=False, exact_coefficient_membership=False,
                  producer_go=False, rh_claim=False)
    output = ROOT / "results/2576_shared_exp_validation.json"
    output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8", newline="\n")
    print("SHARED_EXP_VALIDATED", len(reports), result["build"]["verified_targets"], flush=True)


if __name__ == "__main__":
    main()
