"""Recompute the full owner enclosure and compare an independent precision."""
from fractions import Fraction
import hashlib
import json
from pathlib import Path

from flint import ctx

import routea_owner_whole_cell_2535 as target
import routea_owner_whole_cell_check_2535 as checker
import routea_owner_whole_cell_selftest_2535 as selftest

ROOT = Path(__file__).resolve().parents[1]


def main():
    selftest.main()
    path = ROOT / "results/2535_whole_cell_enclosure.json"
    checked = checker.check(path)
    artifact = json.loads(path.read_text())
    ctx.prec = artifact["precision_bits"]
    families = target.load_families()
    for old in artifact["endpoints"]:
        new = target.run_grid(families, old["cells"], Fraction(old["sigma_exact"]), True)
        assert new == old, "same-precision exact payload changed"
    ctx.prec = 256
    families = target.load_families()
    deltas = []
    for old in artifact["endpoints"]:
        new = target.run_grid(families, old["cells"], Fraction(old["sigma_exact"]), False)
        delta = abs(Fraction(new["total_upper_exact"])-Fraction(old["total_upper_exact"]))
        # Stability control only; validity comes from balls and the analytic bound.
        assert delta < Fraction(1, 10**35)
        assert new["fits_pin"]
        deltas.append(str(delta))
    baseline_path = ROOT / "results/2533_signed_grid_refinement_probe.json"
    baseline = json.loads(baseline_path.read_text())
    assert baseline["repair_sha256"] == artifact["input_sha256"]["results/2338_exact_interpolation_repair.json"]
    assert baseline["capture_sha256"] == artifact["input_sha256"]["results/2275_gap_owner_audit.json"]
    node_deltas = []
    for old, sign in zip(artifact["endpoints"], ("-0.5", "0.5")):
        reference = Fraction(baseline["grids"][str(old["cells"])][sign]["node_sum"])
        delta = Fraction(old["node_upper_exact"])-reference
        assert 0 <= delta < Fraction(1, 10**35)
        node_deltas.append(str(delta))
    # Negative test: a changed coordinate must not pass the arithmetic checker.
    import tempfile
    broken = json.loads(path.read_text())
    broken["endpoints"][0]["rows"][1]["left_exact"] = "0"
    with tempfile.TemporaryDirectory() as tmp:
        tampered = Path(tmp)/"tampered.json"
        tampered.write_text(json.dumps(broken), encoding="utf-8")
        try:
            checker.check(tampered)
        except AssertionError:
            pass
        else:
            raise AssertionError("tampered coordinate accepted")
    result = dict(record=2535, status="VALIDATION_PASS", exact_payload_check=checked,
                  same_precision_full_replay_identical=True,
                  precision_192_vs_256_total_deltas_exact=deltas,
                  node_upper_minus_2533_diagnostic_exact=node_deltas,
                  tampered_coordinate_rejected=True,
                  artifact_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                  validation_source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  lean_numeric_certificate=False)
    out = ROOT/"results/2535_whole_cell_validation.json"
    out.write_text(json.dumps(result, indent=2)+"\n", encoding="utf-8")
    print(json.dumps(result), flush=True)


if __name__ == "__main__":
    main()
