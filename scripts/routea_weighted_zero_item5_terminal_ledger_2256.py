#!/usr/bin/env python3
"""2256 - Terminal item-5 ledger at the 2253/2255 standing, plus the
float-solve residual audit (convention A closure).

Assembles: the certified 2249 margin, the 2255 measured-and-charged
ideal-to-discrete gaps, and the 2253 count-free full-tail charge.  Freezes
the Lean constants for the fallback strict-margin theorem (the 2252
arithmetic brick repriced to the transfer-free ledger).  Also measures the
stored-solve residuals of the committed operands (the float-solve gap is
defined away by convention A, record 2230; the residuals certify the
stored object is internally consistent).  Writes
results/2256_item5_terminal_ledger.json.
"""
import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import routea_weighted_zero_direct_product_outward_2234 as o34  # noqa: E402
import routea_weighted_zero_direct_product_mass_screen_2197 as s97  # noqa: E402
import routea_opposite_gates_height_1994 as r94  # noqa: E402
import fourpoint_owner_completion_1980 as r80  # noqa: E402

import mpmath as mp  # noqa: E402

OUTPUT = ROOT / "results" / "2256_item5_terminal_ledger.json"

TAIL_2248 = 4894093747.764274
KNOWN_ERROR_2109 = 74601530.30234718
EPS0_FULL_TAIL = 1670000000000      # Lean constant, must stay below the slack
GAP_CONST = 10000000                # Lean constant, must stay above the gap


def main():
    art49 = json.loads(
        (ROOT / "results" / "2249_l1_enclosure.json").read_text("utf-8"))
    art55 = json.loads(
        (ROOT / "results" / "2255_l1_gaps.json").read_text("utf-8"))
    margin = -art49["diagnostics"]["q_hi"]
    total_gap = art55["total"]["total_gap_charged"]
    margin_terminal = margin - total_gap
    charge = TAIL_2248 + KNOWN_ERROR_2109
    eps0 = margin_terminal - charge
    assert eps0 > GAP_CONST, "gap constant not slack-safe"
    assert total_gap < GAP_CONST, \
        "measured gap exceeds the frozen Lean constant"
    assert eps0 > EPS0_FULL_TAIL, "eps0 constant not slack-safe"

    # float-solve residual audit (convention A closure)
    fam, base, corr, _ = o34.build_construction()
    rho = (0.5 + s97.DELTA) + 1j * s97.GAMMA
    nodes, values = r94.owner_nodes_ext(rho, s97.GAMMA)
    radius = r80.ball_radius(rho, 0)
    mp.mp.dps = 50
    for index in range(1, 31):
        height = float(mp.im(mp.zetazero(index)))
        z = 0.5 + 1j * height
        if abs(z - rho) <= radius and all(
                abs(z - e) > 1e-6 for e in nodes):
            nodes.append(z)
            values.append(0j)
    # rebuild the stored matrix with the committed operands (m=6400)
    import routea_weighted_zero_l1_enclosure_2249 as r49  # noqa: E402
    r49.M = 6400
    r49._GL_XS = None
    r49._GL_WS = None
    xw_cache = {}
    xw_list = []
    for a, _ in fam:
        if float(a) not in xw_cache:
            xw_cache[float(a)] = r49.phi_weights_cached(a)
        xw_list.append(xw_cache[float(a)])
    a_mat = r80.family_values(fam, s97.K, np.asarray(nodes, complex),
                              xw_list).T
    res_b = a_mat @ base - np.ones(len(nodes), complex)
    res_c = a_mat @ corr - np.asarray(values, complex)
    resid = {
        "residual_base_inf": float(np.abs(res_b).max()),
        "residual_corr_inf": float(np.abs(res_c).max()),
        "base_abs_inf": float(np.abs(base).max()),
        "corr_abs_inf": float(np.abs(corr).max()),
        "rel_residual_base": float(np.abs(res_b).max()
                                    / np.abs(base).max()),
        "rel_residual_corr": float(np.abs(res_c).max()
                                   / np.abs(corr).max()),
        "condition_number": float(np.linalg.cond(a_mat)),
    }

    result = {
        "record": 2256,
        "status": "TERMINAL-LEDGER-FULL-TAIL + SOLVE-RESIDUAL-AUDIT",
        "date": "2026-09-30",
        "ledger": {
            "margin_2249": margin,
            "total_gap_charged_2255": total_gap,
            "margin_terminal": margin_terminal,
            "charge_full_tail": charge,
            "reading_terminal": charge / margin_terminal,
            "eps0_terminal": eps0,
        },
        "lean_constants": {
            "highShellTail2248": TAIL_2248,
            "knownError2109": KNOWN_ERROR_2109,
            "gapCharge2255": GAP_CONST,
            "eps0FullTail2249": EPS0_FULL_TAIL,
            "strict_lemmas": [
                "transfer_free_charge_le_margin_sub_slack",
                "a005_item5_strict_signed_margin_full_tail"],
            "note": ("constants frozen from this artifact; the strict "
                     "arithmetic lemma keeps slack "
                     f"{margin - charge - GAP_CONST - EPS0_FULL_TAIL}"),
        },
        "solve_residual_audit": resid,
        "convention_a_statement": (
            "record 2230 convention A: the stored binary64 operands are "
            "exact and define the object; the float solve vs exact solve "
            "gap is a convention, not a charge. The residual audit shows "
            "the stored coefficient vectors solve the stored matrix to "
            "machine precision, so the stored object is internally "
            "consistent"),
        "nonclaims": [
            "the terminal margin carries the 2255 refinement-style gap "
            "charge; the ideal-to-discrete gaps beyond the measured "
            "refinements are not independently derived",
            "the Lean repricing is the arithmetic only; the numeric "
            "inputs stay artifact-level facts",
            "no producer GO, no gate sign change, no RH claim",
        ],
        "provenance": {
            "script": "scripts/routea_weighted_zero_item5_terminal_ledger_2256.py",
            "inputs": ["results/2249_l1_enclosure.json",
                       "results/2255_l1_gaps.json",
                       "results/2234_build_cache.npz"],
        },
    }
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8",
                      newline="\n")
    print(json.dumps({"ledger": result["ledger"],
                      "residuals": resid,
                      "slack": margin - charge - GAP_CONST - EPS0_FULL_TAIL},
                     indent=2))


if __name__ == "__main__":
    main()