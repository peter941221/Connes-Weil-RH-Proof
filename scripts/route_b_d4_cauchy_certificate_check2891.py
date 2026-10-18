"""Cross-check the Route B D4 Cauchy enclosure and remainder artifacts."""
import json
import os
import hashlib
from pathlib import Path
from fractions import Fraction


def load(name):
    override = os.environ.get("D4_CAUCHY_REMAINDER_OVERRIDE") if "2890" in name else None
    path = Path(override) if override else Path("results", name)
    return json.loads(path.read_text(encoding="utf-8"))


def generator_hash(script):
    return hashlib.sha256(Path("scripts", script).read_bytes()).hexdigest()


def main():
    interval = load("2889_route_b_d4_cauchy_interval.json")
    remainder = load("2890_route_b_d4_cauchy_remainder.json")
    rows = interval["rows"]
    ordered = sorted(rows, key=lambda row: row["angle_cells"])
    finest = ordered[-1]
    sampled_upper = Fraction(str(finest["rigorous_rectangle_upper"]))
    declared_M = Fraction(remainder["M"])
    ratio = Fraction(remainder["r_over_R"])
    declared_tail = Fraction(remainder["remainder_bound"])
    recomputed_tail = declared_M * ratio**22 / (1 - ratio)
    checks = {
        "all_interval_rows_are_positive": all(
            Fraction(str(row["rigorous_rectangle_upper"])) > 0
            for row in ordered
        ),
        "refinement_does_not_increase_upper_bound": all(
            ordered[i + 1]["rigorous_rectangle_upper"] <=
            ordered[i]["rigorous_rectangle_upper"]
            for i in range(len(ordered) - 1)
        ),
        "finest_interval_is_below_declared_M": sampled_upper <= declared_M,
        "remainder_formula_replays": declared_tail == recomputed_tail,
        "tail_below_truncation_margin": declared_tail < Fraction(remainder["truncated_lower_bound"]),
        "interval_artifact_marks_nonformal": interval["claims"]["full_cauchy_remainder_certificate"] is False,
        "remainder_artifact_marks_nonformal": remainder["claims"]["formal_analytic_bridge"] is False,
        "interval_generator_hash_matches": interval.get("generator_sha256") == generator_hash("route_b_d4_cauchy_interval2889.py"),
        "remainder_generator_hash_matches": remainder.get("generator_sha256") == generator_hash("route_b_d4_cauchy_remainder2890.py"),
    }
    payload = {"record": 2891, "checks": checks,
               "all_checks_pass": all(checks.values()),
               "claims": {"artifact_consistency": all(checks.values()),
                          "formal_cauchy_proof": False}}
    out = Path("results/2891_route_b_d4_cauchy_certificate_check.json")
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(payload, indent=2))
    if not payload["all_checks_pass"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
