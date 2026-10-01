"""Audit the source path used to construct directed point terms.

This is a source-level control bound to the 2385 artifact hash.  It verifies
that the worker's directed branch uses the MPFR term, converts it with RNDU,
and accumulates with RNDU, while the ordinary ``math.hypot`` diagnostic branch
is not used for the directed value.  It is not a proof of the MPFR evaluator's
mathematical enclosure theorem.
"""

from __future__ import annotations

import ast
import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def calls_in(node: ast.AST, name: str) -> list[ast.Call]:
    return [candidate for candidate in ast.walk(node)
            if isinstance(candidate, ast.Call)
            and isinstance(candidate.func, ast.Name)
            and candidate.func.id == name]


def main() -> dict:
    artifact_path = ROOT / "results/2385_shared_geometry_776611.json"
    source_path = ROOT / "scripts/routea_nodal_interval_fullgrid_2359.py"
    evaluator_path = ROOT / "scripts/routea_weighted_zero_zero_count_certificate_2242.py"
    artifact = json.loads(artifact_path.read_text())
    source_text = source_path.read_text()
    tree = ast.parse(source_text, filename=str(source_path))
    worker = next(node for node in tree.body
                  if isinstance(node, ast.FunctionDef)
                  and node.name == "worker_span")
    worker_text = ast.get_source_segment(source_text, worker) or ""

    require(artifact["source_sha256"] == sha256(source_path),
            "2359 source hash mismatch")
    require(artifact["evaluator_source_sha256"] == sha256(evaluator_path),
            "2242 evaluator source hash mismatch")
    require("kernel.eval_box" in worker_text,
            "worker does not call the interval kernel")
    require("_WORKER_POINT_NORM" in worker_text and
            "_WORKER_POINT_EXP" in worker_text,
            "directed point norm/weight objects absent")
    require("_WORKER_POINT_TERM.get_d(_WORKER_INTERVAL.RNDU)" in worker_text,
            "MPFR term is not converted with RNDU")
    require("_WORKER_DIRECTED_FLOAT_ACC" in worker_text and
            "_WORKER_INTERVAL.RNDU" in worker_text,
            "directed binary64 accumulator path absent")
    require(worker_text.count("interval_abs_upper") == 1 and
            "term = cell_weight * interval_abs_upper(bounds) * factor" in worker_text,
            "measurement modulus is not isolated to the diagnostic assignment")
    require("directed_term_binary64_roundup_integrals" in source_text,
            "final directed roundup fields absent")

    result = {
        "record": 2395,
        "status": "DIRECTED_TERM_CONSTRUCTION_PATH_AUDIT_PASS",
        "source_hashes_match": True,
        "kernel_point_box_path_present": True,
        "mpfr_term_to_binary64_rndu_present": True,
        "directed_binary64_accumulation_rndu_present": True,
        "measurement_hypot_excluded_from_directed_worker": True,
        "numeric_term_dominance_theorem_proved": False,
        "lean_numeric_imported": False,
        "producer_go": False,
        "rh_claim": False,
    }
    output = ROOT / "results/2395_directed_term_path_audit.json"
    output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))
    return result


if __name__ == "__main__":
    main()
