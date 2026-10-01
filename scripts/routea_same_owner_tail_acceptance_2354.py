"""2354: exact same-source scalar acceptance lanes; no gate or prefix import."""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path

import routea_same_owner_premise_audit_2352 as premise

ROOT = Path(__file__).resolve().parents[1]
SUPPLIER = ROOT / "results/2353_same_owner_tail_supplier.json"
MULTIPLICITY_CAP = Fraction(2573, 20)
RHO_NORM_CAP = Fraction(41)
D4_CAP = Fraction(746785658244)
D2_CAP = Fraction(71280628476)
RESERVE = Fraction(3, 2)


def verify_hashes(payload, root=ROOT):
    for key in ("source_sha256", "input_sha256"):
        for relative, expected in payload[key].items():
            if hashlib.sha256((root / relative).read_bytes()).hexdigest() != expected:
                raise ValueError("supplier provenance mismatch: " + relative)


def get_dyadic_contraction(upper):
    upper = Fraction(upper)
    if not 0 < upper < 1:
        raise ValueError("a positive subunit upper is required")
    exponent = 0
    while Fraction(1, 2 ** (exponent + 1)) >= upper:
        exponent += 1
    return exponent, Fraction(1, 2**exponent)


def get_acceptance_ratio(q, iterate, shell, coefficient, rho_norm=RHO_NORM_CAP,
                         d4=D4_CAP, d2=D2_CAP, mass=1, reserve=RESERVE):
    q, coefficient, rho_norm, d4, d2, mass, reserve = map(
        Fraction, (q, coefficient, rho_norm, d4, d2, mass, reserve))
    if not isinstance(iterate, int) or iterate < 0 or not isinstance(shell, int) or shell < 0:
        raise ValueError("nonnegative integer iterate and shell required")
    if not 0 < q < 1 or coefficient <= 0 or rho_norm < 0 or d4 <= 0 or d2 <= 0 or mass <= 0 or reserve <= 1:
        raise ValueError("invalid positive acceptance parameters")
    orbit = (3 + rho_norm) ** 4
    return (reserve * 4 * MULTIPLICITY_CAP * Fraction(3, 4)**shell * orbit *
            (1 + orbit / coefficient)**2 * (q**iterate * d4 * d2)**2 / mass)


def get_ratio_row(q, iterate, shell, coefficient):
    ratio = get_acceptance_ratio(q, iterate, shell, coefficient)
    return {"iterate": iterate, "shell": shell, "lambda_exact": str(coefficient),
            "ratio_exact": str(ratio), "ratio_display": format(float(ratio), ".12e"),
            "registered_scalar_budget_pass": ratio < 1,
            "not_a_gate_row": True, "actual_tail_acceptance_instantiated": False}


def run(supplier_path=SUPPLIER):
    supplier = json.loads(supplier_path.read_text())
    verify_hashes(supplier)
    if supplier["record"] != 2353 or not supplier["T128_uniform_bound_proved"]:
        raise ValueError("unexpected supplier status")
    if supplier["owner_changed"] or supplier["certified_base_threshold_exact"] != "128":
        raise ValueError("supplier owner or threshold changed")
    checked = premise.run()
    witness = json.loads(premise.WITNESS.read_text())
    if supplier["input_sha256"]["results/2351_moment_matrix_witness.json"] != hashlib.sha256(premise.WITNESS.read_bytes()).hexdigest():
        raise ValueError("supplier and premise owners differ")
    rho = checked["mandatory_targets"]
    rho_norm_upper = abs(Fraction(rho["rho_real_exact"])) + abs(Fraction(rho["rho_imag_exact"]))
    d4 = Fraction(supplier["whole_line_angular_constants_exact"]["base_order4"])
    d2 = Fraction(supplier["whole_line_angular_constants_exact"]["correction_order2"])
    if rho_norm_upper > RHO_NORM_CAP or d4 > D4_CAP or d2 > D2_CAP:
        raise ValueError("registered outward caps failed")
    exponent, q = get_dyadic_contraction(supplier["contour_base_upper_T128_exact"])
    if exponent != 52:
        raise ValueError("unexpected strongest containing dyadic contraction")
    rows = [{"q_exact": str(bound), **get_ratio_row(bound, iterate, 6, coefficient)}
            for bound in (Fraction(1, 2**14), q)
            for iterate in (0, 1, 2, 3, 7, 8)
            for coefficient in (Fraction(1), Fraction(256), Fraction(1, 10**13))]
    lanes = [get_ratio_row(q, 2, 6, Fraction(256)),
             get_ratio_row(q, 3, 6, Fraction(1, 10**13))]
    if not all(row["registered_scalar_budget_pass"] for row in lanes):
        raise ValueError("registered acceptance lanes failed")
    sources = ["scripts/routea_same_owner_tail_acceptance_2354.py",
               "scripts/routea_same_owner_tail_acceptance_selftest_2354.py",
               "ConnesWeilRH/Dev/C1RouteATailAcceptance.lean",
               "ConnesWeilRH/Dev/C1RouteATailAcceptanceAudit.lean",
               "ConnesWeilRH/Dev/C1FourPointHighShellTail.lean",
               "ConnesWeilRH/Dev/C1FourPointContradictionAssembly.lean",
               "ConnesWeilRH/Dev/C1RouteAMultiplicityBound.lean"]
    return {"record": 2354, "status": "EXACT_CONDITIONAL_SAME_OWNER_SCALAR_ACCEPTANCE_LANES",
            "source_sha256": {relative: hashlib.sha256((ROOT / relative).read_bytes()).hexdigest() for relative in sources},
            "input_sha256": {str(supplier_path.relative_to(ROOT)): hashlib.sha256(supplier_path.read_bytes()).hexdigest(),
                             "results/2351_moment_matrix_witness.json": hashlib.sha256(premise.WITNESS.read_bytes()).hexdigest()},
            "parent_moment_witness_rechecked_same_run": True, "supplier_hashes_verified": True,
            "source_formula": "H=B^(n+1)C; v=fullOrbitAnnihilator(g,rho)-lambda*g; no extra P-only factor",
            "supplier_scope": supplier["supplier_scope"],
            "rho_norm_bound_method": "norm <= abs(real)+abs(imag) on exact stored coordinates",
            "rho_norm_upper_exact": str(rho_norm_upper), "rho_norm_registered_cap_exact": str(RHO_NORM_CAP),
            "D4_cap_exact": str(D4_CAP), "D2_cap_exact": str(D2_CAP),
            "multiplicity_cap_exact": str(MULTIPLICITY_CAP),
            "multiplicity_cap_theorem": "C1RouteAMultiplicityBound.spectralMultiplicityConstant_le_coarse",
            "q_dyadic_exponent": exponent, "q_exact": str(q),
            "q_selection": "smallest dyadic upper containing the same 2353 analytic bound; no function change",
            "threshold_exact": "128", "shell": 6, "shell_ceiling_exact": "128",
            "rho_double_height_exact": str(2 * abs(Fraction(rho["rho_imag_exact"]))),
            "epsilon_square_reserve_exact": str(RESERVE),
            "acceptance_formula": "ratio=(3/2)*4*K*(3/4)^N*(3+R)^4*(1+(3+R)^4/lambda)^2*(q^n D4 D2)^2/m",
            "acceptance_mass_floor_exact": "1",
            "reserve_meaning": "epsilon^2=(3/2)*A makes A<epsilon^2 strict; scalar ratio<1 is sufficient only with all source/prefix premises",
            "parameter_rows": rows,
            "positive_lambda_lanes": [{**row, "all_lambda_at_or_above_anchor": True,
                                       "coefficient_monotonicity_lean_proved": True} for row in lanes],
            "support_covers": [premise.get_support_cover([Fraction(value) for value in witness["support_radii_exact"]], iterate)
                               for iterate in (2, 3, 8)],
            "required_prefix": "sourceNontrivialZerosInClosedBallFinset rho (2^(N+1)+2+dist(2,rho)) union routeNodes",
            "captured_node_count": checked["captured_node_count"],
            "failed_sufficient_bound_is_actual_tail_no_go": False,
            "actual_gate_row_paired": False, "tail_supplier_imported_in_lean": False,
            "actual_numeric_coefficients_imported_in_lean": False,
            "fourth_order_spectral_tail_instantiated": False,
            "complete_zero_prefix_instantiated": False, "rho_is_source_zero_proved": False,
            "full_signed_kernel_priced": False, "healthy_detector_instantiated": False,
            "owner_changed": False, "map103_reopened": False, "producer_go": False, "rh_claim": False}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=ROOT / "results/2354_same_owner_tail_acceptance.json")
    arguments = parser.parse_args()
    result = run()
    arguments.output.write_text(json.dumps(result, indent=2) + "\n")
    print(result["status"], "q", result["q_exact"], "lanes", len(result["positive_lambda_lanes"]))
