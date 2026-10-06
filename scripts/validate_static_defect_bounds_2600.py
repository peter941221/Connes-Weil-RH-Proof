"""Independent exact validator for the 2600 static defect comparison."""
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import routea_moment_matrix_exact_check_2351 as checker

WITNESS = ROOT / "results/2351_moment_matrix_witness.json"
CHECK = ROOT / "results/2351_moment_matrix_exact_check.json"
OUTPUT = ROOT / "results/2600_static_defect_comparison_validation.json"


def main() -> None:
    payload = json.loads(WITNESS.read_text())
    matrix = [[checker.complex_interval(value) for value in row] for row in payload["matrix"]]
    inverse = [[checker.complex_interval(value) for value in row] for row in payload["candidate_inverse"]]
    product = [[checker.sum_complex(
        checker.complex_mul(inverse[row][k], matrix[k][column])
        for k in range(30)) for column in range(30)] for row in range(30)]
    defect = [[checker.complex_add(checker.point(int(row == column)),
                                  checker.complex_neg(product[row][column]))
               for column in range(30)] for row in range(30)]
    bounds = [[checker.l1_upper(value) for value in row] for row in defect]
    row_sums = [sum(row, checker.Fraction(0)) for row in bounds]
    committed = json.loads(CHECK.read_text())
    if [str(value) for value in row_sums] != committed["row_bounds_exact"]:
        raise ValueError("row sums differ from committed 2351 exact check")
    serialized = json.dumps([[str(value) for value in row] for row in bounds], separators=(",", ":"))
    result = {
        "record": 2600,
        "rows": 30,
        "entries": 900,
        "exact_fraction_reconstruction": True,
        "row_sums_match_2351": True,
        "entry_bound_digest": hashlib.sha256(serialized.encode()).hexdigest(),
        "witness_sha256": hashlib.sha256(WITNESS.read_bytes()).hexdigest(),
        "lean_file": "ConnesWeilRH/Dev/C1RouteACorrectionStaticDefectBounds2600.lean",
        "lean_verified": False,
        "analytic_interval_soundness": "external_premise_required",
        "producer_go": False,
        "rh_claim": False,
    }
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
