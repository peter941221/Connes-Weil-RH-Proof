#!/usr/bin/env python3
"""Record 2721B artifact-side checker for the wired row-B contradiction
module ConnesWeilRH/Dev/C1FourPointRowBWired2721.lean.

Binds the Lean pins to the committed artifact renders (records 2720,
2718, 2354) with exact rational arithmetic, re-derives the two scalar
acceptance chains in exact Fractions, guards the statement
transcription against the committed Lean source, parses the axiom
census evidence, and runs mutation controls (record 2310/2311
discipline).

Usage: python3 scripts/check_four_point_wired_2721.py
Exit 0 iff every check passes. Artifact: results/2721b_wired_check.json
"""

import json
import sys
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
RESULTS = ROOT / "results"
LEAN_MAIN = ROOT / "ConnesWeilRH" / "Dev" / "C1FourPointRowBWired2721.lean"
LEAN_AUDIT = ROOT / "ConnesWeilRH" / "Dev" / "C1FourPointRowBWired2721Audit.lean"

TRIO = sorted(["propext", "Classical.choice", "Quot.sound"])

# Lean pins (exact rationals, transcribed from the committed defs)
PIN_Q = Fraction(26, 10**17)
PIN_C4 = Fraction(61000000)
PIN_C2 = Fraction(29000000)
PIN_RHO_NORM = Fraction(22)
PIN_RHO_IM = Fraction(421, 20)
PIN_MULT = Fraction(515)
PIN_LAMBDA = Fraction(24)

DEF_LINES = {
    "q": "def wiredQRowB2721 : Real := 26 / 10 ^ 17",
    "C4": "def wiredC4RowB2721 : Real := 61000000",
    "C2": "def wiredC2RowB2721 : Real := 29000000",
    "rho_norm": "def wiredRhoNormCapRowB2721 : Real := 22",
    "rho_im": "def wiredRhoImCapRowB2721 : Real := 421 / 20",
    "mult": "def wiredMultCapRowB2721 : Real := 515",
}

CONSUMER_NAMES = [
    "selectedOwner_fullOrbit_span_fourthOrderSpectralTail_of_q",
    "qw_neg_of_spectralHeightShellPrefix_and_coefficient_scaled_tail",
    "annihilatorDetectorSpanVector_qw_nonneg_of_gate",
    "false_of_qw_nonneg_and_neg",
    "annihilator_span_gate_eq_parabola",
    "orbitWindowSemiLocalGate_iff",
    "xiMultiplicity_pos",
    "fullFunctionalEquationOrbitAnnihilator_support_subset_Icc",
    "fullFunctionalEquationOrbitAnnihilator_vanishesOn_cc20Triple",
]


def ulp(x: float) -> Fraction:
    """Half-ulp scale of a positive float render (2^-52 * |x|)."""
    return Fraction(abs(x)) * Fraction(2) ** -52


def sci(fr: Fraction) -> str:
    return f"{float(fr):.6e}"


def main() -> int:
    checks = []

    def check(name, ok, detail):
        checks.append({"check": name, "ok": bool(ok), "detail": detail})
        return ok

    # ---------- load artifacts ----------
    try:
        a2720 = json.loads((RESULTS / "2720_p3_certified_strip_constants.json").read_text())
        a2718 = json.loads((RESULTS / "2718_gate_sign_rig.json").read_text())
        a2354 = json.loads((RESULTS / "2354_same_owner_tail_acceptance.json").read_text())
        census = json.loads((RESULTS / "2721b_axiom_census.json").read_text())
    except (OSError, json.JSONDecodeError) as exc:
        print(f"FAIL artifact load: {exc}")
        return 1

    rowB = next(r for r in a2720["rows"] if abs(r["gamma"] - 21.022039638771556) < 1e-9)
    rowB2718 = next(
        r for r in a2718["rows"] if abs(r["gamma"] - 21.022039638771556) < 1e-9
    )
    src = LEAN_MAIN.read_text(encoding="utf-8")
    audit_src = LEAN_AUDIT.read_text(encoding="utf-8")

    # ---------- 1. pin domination vs artifact renders ----------
    q_star = Fraction(rowB["certified"]["q_star_T64"])
    check(
        "pin_q_dominates_q_star_T64",
        PIN_Q > q_star and (PIN_Q - q_star) >= 100 * ulp(rowB["certified"]["q_star_T64"]),
        f"pin {sci(PIN_Q)} > render {sci(q_star)}, slack {sci(PIN_Q - q_star)} "
        f"({float((PIN_Q - q_star) / ulp(rowB['certified']['q_star_T64'])):.3e} ulp)",
    )

    C4_star = Fraction(rowB["certified"]["C4_star"])
    check(
        "pin_C4_dominates_C4_star",
        PIN_C4 >= C4_star and (PIN_C4 - C4_star) >= 100 * ulp(rowB["certified"]["C4_star"]),
        f"pin {PIN_C4} >= render {sci(C4_star)}, slack {sci(PIN_C4 - C4_star)} ulp-scale ok",
    )

    C2_star = Fraction(rowB["certified"]["C2_star_corr"])
    check(
        "pin_C2_dominates_C2_star_corr",
        PIN_C2 >= C2_star
        and (PIN_C2 - C2_star) >= 100 * ulp(rowB["certified"]["C2_star_corr"]),
        f"pin {PIN_C2} >= render {sci(C2_star)}, slack {sci(PIN_C2 - C2_star)} ulp-scale ok",
    )

    mult_cap = Fraction(a2354["multiplicity_cap_exact"])
    check(
        "pin_mult_dominates_2354_cap",
        PIN_MULT >= mult_cap,
        f"pin {PIN_MULT} >= 2354 cap {mult_cap} ({sci(mult_cap)}) via "
        f"{a2354['multiplicity_cap_theorem']}",
    )

    re_rho = Fraction(rowB["rho"][0])
    im_rho = Fraction(rowB["rho"][1])
    check(
        "pin_rho_norm_dominates_triangle_bound",
        PIN_RHO_NORM > re_rho + im_rho,
        f"triangle bound {sci(re_rho + im_rho)} = |{sci(re_rho)}| + |{sci(im_rho)}| < {PIN_RHO_NORM}",
    )
    check(
        "pin_rho_im_dominates_gamma2",
        PIN_RHO_IM > im_rho,
        f"pin {PIN_RHO_IM} = 21.05 > |Im rho| {sci(im_rho)}",
    )

    lam_min = Fraction(rowB["branch_2718"]["lambda_min"])
    check(
        "pin_lambda_covers_branch_all",
        rowB["branch_2718"]["branch"] == "all"
        and rowB["branch_2718"].get("branch_robust", True)
        and PIN_LAMBDA > lam_min,
        f"branch 'all' (parabola <= 0 at every lambda > 0), lambda_min "
        f"{float(lam_min)} < pin {PIN_LAMBDA}; 2718 row branch_center "
        f"{rowB2718['branch_center']}, robust {rowB2718['branch_robust']}",
    )

    n3 = next(nr for nr in rowB["repricing"]["n_table"] if nr["n"] == 3)
    check(
        "tail_closes_at_own_index_n3",
        rowB["repricing"]["T_pair"] == 64 and n3["joint_pair"],
        f"2720 row B: T_pair {rowB['repricing']['T_pair']}, n=3 joint_pair "
        f"{n3['joint_pair']}, lam_min_pair {n3['lam_min_pair']:.3e}",
    )

    # ---------- 2. exact scalar acceptance re-derivation ----------
    pi_pin = Fraction(4 * 10**9)
    lhs = (
        Fraction(25) ** 4
        * (Fraction(25) ** 4 + 24) ** 2
        * pi_pin
        * (PIN_Q**3 * (PIN_C4 * PIN_C2)) ** 2
    )
    check(
        "hsmall_pi_pin_chain_exact",
        lhs < 1,
        f"25^4 (25^4+24)^2 (4e9) (q^3 C4 C2)^2 = {sci(lhs)} < 1 "
        f"(margin {sci(1 - lhs)}); (44/7)^12 = "
        f"{sci(Fraction(44, 7) ** 12)} < 4e9 ok",
    )
    check(
        "pi_exponent_bound_exact",
        Fraction(44, 7) ** 12 < pi_pin,
        f"(44/7)^12 = {sci(Fraction(44, 7) ** 12)} < {pi_pin}",
    )

    eta = 4 * Fraction(1, 24) ** 2 * PIN_MULT * Fraction(3, 4) ** 5
    check(
        "eta_budget_exact",
        eta < 1 and eta == Fraction(13905, 16384),
        f"4 (1/24)^2 * 515 * (3/4)^5 = {eta} = 13905/16384 = {float(eta):.6f} < 1",
    )
    check(
        "rho_height_chain_exact",
        2 * PIN_RHO_IM < 64,
        f"2 * 421/20 = {float(2 * PIN_RHO_IM)} < 64 = 2^(5+1)",
    )

    # ---------- 3. statement transcription guards ----------
    for key, line in DEF_LINES.items():
        check(f"def_literal_{key}", src.count(line) == 1, f"'{line}' exactly once")
    for name in CONSUMER_NAMES:
        check(f"consumer_{name}", src.count(name) >= 1, "present in main module")
    audit_prints = [
        "wiredHsmallTailRowB2721",
        "wiredEtaBudgetRowB2721",
        "fourPointContradictionRowBWired2721",
    ]
    for decl in audit_prints:
        check(
            f"audit_print_{decl.split('RowB')[0]}",
            audit_src.count(f"#print axioms {decl}") == 1,
            "audit module prints axioms once",
        )

    # ---------- 4. axiom census evidence ----------
    cens = census["census"]
    check(
        "census_trio_all_decls",
        len(cens) == 3 and all(sorted(v) == TRIO for v in cens.values()),
        f"{list(cens.values())} all exactly the standard trio",
    )
    check(
        "census_build_green",
        census["footer_green"]
        and census["error_lines"] == 0
        and census["sorry_lines"] == 0,
        f"footer green={census['footer_green']}, errors={census['error_lines']}, "
        f"sorry={census['sorry_lines']}",
    )

    # ---------- 5. mutation controls (each must FIRE) ----------
    check(
        "mutation_q_pin_below_render_fires",
        not (Fraction(25, 10**17) > q_star),
        "q pin 25/10^17 < render -> domination check fails (control fires)",
    )
    check(
        "mutation_mult_below_cap_fires",
        not (Fraction(128) >= mult_cap),
        f"mult pin 128 < 2354 cap {float(mult_cap)} -> check would fail (control fires)",
    )
    check(
        "mutation_C4_C2_swap_fires",
        not (PIN_C2 >= C4_star),
        f"C2 pin {PIN_C2} < C4* {sci(C4_star)} -> swapped pin would fail (control fires)",
    )

    # ---------- verdict ----------
    ok_all = all(c["ok"] for c in checks)
    payload = {
        "record": "2721B",
        "date": "2026-10-16",
        "status": "PASS" if ok_all else "FAIL",
        "checks": checks,
        "nonclaims": [
            "conditional theorem: hypotheses (strip envelopes, g-construction, "
            "gate corner at lambda=24, shell prefix) remain open obligations",
            "no producer GO, no map-103 reopening, no RH claim",
        ],
        "provenance": {
            "lean_main": str(LEAN_MAIN.name),
            "lean_audit": str(LEAN_AUDIT.name),
            "artifacts": [
                "results/2720_p3_certified_strip_constants.json",
                "results/2718_gate_sign_rig.json",
                "results/2354_same_owner_tail_acceptance.json",
                "results/2721b_axiom_census.json",
            ],
        },
    }
    (RESULTS / "2721b_wired_check.json").write_text(
        json.dumps(payload, indent=1) + "\n", encoding="utf-8"
    )
    print(f"{'PASS' if ok_all else 'FAIL'}: {sum(c['ok'] for c in checks)}/{len(checks)} checks")
    for c in checks:
        if not c["ok"]:
            print(f"  FAILED: {c['check']}: {c['detail']}")
    return 0 if ok_all else 1


if __name__ == "__main__":
    sys.exit(main())
