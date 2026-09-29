#!/usr/bin/env python3
"""2248 - Lean multiplicity-constant tightening: absorption 192 -> 72.

`ConnesWeilRH/Dev/C1SpectralSummability.lean` previously absorbed the sharp
`R log R` dyadic exponent with the flat rung constant `192 * 3^n`; the new
lemma `two_mul_add_four_add_rlogr_le_three_pow` proves
`2 (n+4) + (n+4) 2^(n+4) <= 72 * 3^n` with `72` the exact supremum of the
ratio (attained at `n = 0`), and the half-plane, sphere, and multiplicity
theorems now carry `72`.  The numeric proxy of the Lean constant

    mult(c) = (xiGrowthFixedConstant + 1 + |log (pi/6)| + c) / log 2

drops from `301.83032993648527` (c = 192) to the c = 72 value, repricing
the Lean high-shell tail `4 * mult * B_upper` against the signed margin.

Writes results/2248_multiplicity_tightening.json.  Screening artifact only.
"""

import json
import math
from pathlib import Path

import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]
R = ROOT / "results"
SIGNED_MARGIN = 1675397327895.099
MULT_OLD_EXPECTED = 301.83032993648527
ARTIFACT_2243 = R / "2243_panel_cem_reprice.json"
ARTIFACT_2245 = R / "2245_owner_count_brick.json"
OUTPUT = R / "2248_multiplicity_tightening.json"
KAPPA = 72


def up_many(v, n):
    for _ in range(n):
        v = math.nextafter(v, math.inf)
    return v


def main():
    mp.mp.dps = 50
    screen = json.loads(ARTIFACT_2243.read_text(encoding="utf-8"))
    brick = json.loads(ARTIFACT_2245.read_text(encoding="utf-8"))
    b_upper = screen["screen"]["B_upper"]
    mult_old = screen["screen"]["spectralMultiplicityConstant"]
    tail_old = screen["screen"]["high_shell_budget_upper"]
    assert mult_old == MULT_OLD_EXPECTED, mult_old

    kernel_small = float((1 / mp.pi) ** mp.mpf("0.25") *
                         mp.gamma(mp.mpf("0.25")))
    xi_tail = float(2 / (1 - mp.e ** -mp.pi))
    xi_growth = 2.0 * xi_tail * (kernel_small + 1.0)
    log_xi2 = float(abs(mp.log(mp.pi / 6)))
    log2 = math.log(2.0)

    def mult(c):
        return (xi_growth + 1.0 + log_xi2 + c) / log2

    check_old = mult(192)
    mult_new = mult(KAPPA)
    assert check_old == MULT_OLD_EXPECTED, (check_old, MULT_OLD_EXPECTED)
    tail_new = up_many(up_many(4.0 * mult_new, 3) * b_upper, 3)
    tail_over_new = tail_new / SIGNED_MARGIN
    tail_over_old = tail_old / SIGNED_MARGIN

    # Supremum check: sup_n (2(n+4) + (n+4) 2^(n+4)) / 3^n = 72 at n = 0.
    ratios = [(2 * (n + 4) + (n + 4) * 2 ** (n + 4)) / 3 ** n
              for n in range(0, 31)]
    sup_n = max(ratios)
    assert sup_n == 72.0, sup_n

    stress = brick["stress"]
    combos = {
        "reading_2119_old_constant":
            (brick["inputs"]["jensen_bound_2119"] /
             brick["inputs"]["screen_nodes_2117"]) * tail_over_old,
        "unconditional_new_constant":
            stress["ratio_unconditional"] * tail_over_new,
        "imported_new_constant":
            stress["ratio_imported"] * tail_over_new,
    }
    result = {
        "record": 2248,
        "status": "MULTIPLICITY-TIGHTENED-72",
        "date": "2026-09-30",
        "lean": {
            "file": "ConnesWeilRH/Dev/C1SpectralSummability.lean",
            "new_lemma": "two_mul_add_four_add_rlogr_le_three_pow",
            "statement": "2 * (n + 4) + (n + 4) * 2 ^ (n + 4) "
                         "<= 72 * 3 ^ n",
            "supremum_check": {"sup_n_0_to_30": sup_n, "attained_at": 0},
            "changed_constants": [
                "norm_completedRiemannXi_le_exp_of_halfplane_dyadic: "
                "192 -> 72",
                "norm_completedRiemannXi_le_exp_on_dyadic_jensen_sphere: "
                "192 -> 72",
                "spectralMultiplicityConstant: 192 -> 72",
                "finiteHeightMultiplicity_dyadic_le: 192 -> 72",
            ],
        },
        "proxy": {
            "xi_growth_fixed_constant": xi_growth,
            "adjusted": 1.0 + log_xi2,
            "abs_log_xi2": log_xi2,
            "kappa": KAPPA,
            "mult_old_c192": check_old,
            "mult_new_c72": mult_new,
            "gain": check_old / mult_new,
        },
        "reprice": {
            "b_upper": b_upper,
            "tail_old": tail_old,
            "tail_new": tail_new,
            "tail_over_margin_old": tail_over_old,
            "tail_over_margin_new": tail_over_new,
            "reading_2119_old_constant": combos["reading_2119_old_constant"],
            "unconditional_new_constant": combos["unconditional_new_constant"],
            "imported_new_constant": combos["imported_new_constant"],
        },
        "nonclaims": [
            "the constant change is a Lean-side strength increase in the "
            "same bound shape (smaller constant); numerical consumers of "
            "the abstract constant remain valid",
            "no producer GO, no gate sign change, no RH claim",
        ],
        "provenance": {
            "script":
                "scripts/routea_weighted_zero_multiplicity_tightening_2248.py",
            "artifact_2243": "results/2243_panel_cem_reprice.json",
            "artifact_2245": "results/2245_owner_count_brick.json",
        },
    }
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n",
                      encoding="utf-8", newline="\n")
    print(json.dumps({"status": result["status"],
                      "proxy": result["proxy"],
                      "reprice": result["reprice"]}, indent=2))


if __name__ == "__main__":
    main()