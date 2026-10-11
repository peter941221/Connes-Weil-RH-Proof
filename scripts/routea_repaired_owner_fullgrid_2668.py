"""Full-grid interval replay using the exact-interpolation repaired owner.

This reuses the 2359 evaluator without changing it. Only the captured
coefficient arrays returned by the 2303 owner loader are replaced by the
float realization of the certified 2338 coefficient-ball midpoints.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import sys
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REPLAY = ROOT / "scripts/routea_nodal_interval_fullgrid_2359.py"
REPAIR = ROOT / "results/2338_exact_interpolation_repair.json"
CAPTURE = ROOT / "results/2275_gap_owner_audit.json"
REPAIR_REREAD = ROOT / "results/2665_l1_margin_repair.json"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def coefficient_arrays(rows):
    base = []
    correction = []
    for row in rows:
        arrays = []
        for name in ("ideal_base_coefficient", "ideal_correction_coefficient"):
            components = {}
            for part in ("real", "imag"):
                ball = row[name][part]
                midpoint = (Fraction(ball["lower_exact"]) +
                            Fraction(ball["upper_exact"])) / 2
                components[part] = float(midpoint)
            arrays.append(complex(components["real"], components["imag"]))
        base.append(arrays[0])
        correction.append(arrays[1])
    return base, correction


def md5_complex(values):
    import numpy as np

    return hashlib.md5(np.ascontiguousarray(values, dtype=complex).tobytes()).hexdigest()


def load_replay_module():
    spec = importlib.util.spec_from_file_location("routea_fullgrid_2668", REPLAY)
    if spec is None or spec.loader is None:
        raise RuntimeError("cannot load the committed 2359 full-grid evaluator")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def run(nodes: int, sigma: float, workers: int, span: int,
        exact_audit: bool):
    repair_payload = json.loads(REPAIR.read_text(encoding="utf-8"))
    capture_payload = json.loads(CAPTURE.read_text(encoding="utf-8"))["owner_capture"]
    reread = json.loads(REPAIR_REREAD.read_text(encoding="utf-8"))
    base, correction = coefficient_arrays(repair_payload["coefficient_rows"])
    repaired_hashes = {"base": md5_complex(base),
                       "correction": md5_complex(correction)}
    expected_hashes = {
        "base": reread["treatment"]["base_md5"],
        "correction": reread["treatment"]["corr_md5"],
    }
    if repaired_hashes != expected_hashes:
        raise AssertionError("reconstructed repair arrays differ from record 2665")
    if repaired_hashes == {"base": capture_payload["base_md5"],
                           "correction": capture_payload["corr_md5"]}:
        raise AssertionError("repair arrays unexpectedly equal captured owner")

    replay = load_replay_module()
    original_load = replay.load

    def load_with_repaired_owner(name, filename):
        loaded = original_load(name, filename)
        if filename == "routea_corrected_strip_envelope_2303.py":
            captured_loader = loaded.load_owner

            def repaired_loader():
                families, _base_capture, _correction_capture, anchors = captured_loader()
                return families, base, correction, anchors

            loaded.load_owner = repaired_loader
        return loaded

    replay.load = load_with_repaired_owner
    result = replay.run(nodes, sigma, workers, span, exact_audit)
    result.update({
        "record": 2668,
        "status": "REPAIRED_OWNER_FULLGRID_REPLAY_NOT_CERTIFICATE",
        "owner_source": "2338 exact-interpolation coefficient-ball midpoints cast to binary64",
        "repair_arrays_match_2665_treatment": True,
        "repaired_coefficient_md5": repaired_hashes,
        "captured_coefficient_md5": {
            "base": capture_payload["base_md5"],
            "correction": capture_payload["corr_md5"],
        },
        "repair_artifact_sha256": sha256(REPAIR),
        "worker_source_sha256": sha256(REPLAY),
        "repair_driver_sha256": sha256(Path(__file__)),
        "pointwise_mathematical_term_dominance_proved": False,
        "trapezoid_remainder_proved": False,
        "lean_imported": False,
        "producer_go": False,
        "rh_claim": False,
    })
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--nodes", type=int, default=240001)
    parser.add_argument("--sigma", type=float, default=-0.5)
    parser.add_argument("--workers", type=int, default=1)
    parser.add_argument("--span", type=int, default=20001)
    parser.add_argument("--skip-exact-audit", action="store_true")
    parser.add_argument("--output", type=Path,
                        default=ROOT / "results/2668_repaired_owner_fullgrid.json")
    args = parser.parse_args()
    result = run(args.nodes, args.sigma, args.workers, args.span,
                 exact_audit=not args.skip_exact_audit)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n",
                           encoding="utf-8")
    print(json.dumps({key: result[key] for key in
                      ("status", "nodes", "workers", "span",
                       "interval_integrals", "directed_term_binary64_roundup_integrals",
                       "repaired_coefficient_md5")}, indent=2))


if __name__ == "__main__":
    main()
