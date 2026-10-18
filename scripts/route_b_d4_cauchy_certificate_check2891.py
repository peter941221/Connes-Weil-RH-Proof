"""Cross-check the Route B D4 Cauchy enclosure and remainder artifacts."""
import json
from pathlib import Path
from fractions import Fraction


def load(name):
    return json.loads(Path("results", name).read_text(encoding="utf-8"))


def main():
    interval = load("2889_route_b_d4_cauchy_interval.json")
    remainder = load("2890_route_b_d4_cauchy_remainder.json")
    rows = interval["rows"]
    finest = max(rows, key=lambda row: row["angle_cells"])
    sampled_upper = Fraction(str(finest["rigorous_rectangle_upper"]))
    declared_M = Fraction(remainder["M"])
    ratio = Fraction(remainder["r_over_R"])
    declared_tail = Fraction(remainder["remainder_bound"])
    recomputed_tail = declared_M * ratio**22 / (1 - ratio)
    checks = {
        "finest_interval_is_below_declared_M": sampled_upper <= declared_M,
        "remainder_formula_replays": declared_tail == recomputed_tail,
        "tail_below_truncation_margin": declared_tail < Fraction(remainder["truncated_lower_bound"]),
        "interval_artifact_marks_nonformal": interval["claims"]["full_cauchy_remainder_certificate"] is False,
        "remainder_artifact_marks_nonformal": remainder["claims"]["formal_analytic_bridge"] is False,
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
