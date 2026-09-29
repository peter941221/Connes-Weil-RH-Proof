#!/usr/bin/env python3
"""Record 2178: explicit algebraic remainder for the fixed-r48 tail.

Decision settled by this probe: replace the zero produced by floating-point
underflow in records 2136/2137 with a closed-form bound for both signs of the
infinite tail.  The bound uses the same one-copy G8-H coefficient path and the
record-2135 variation upper bound.  It does not certify those upstream inputs
or transfer them to the complete closed-ball owner.

For |x| >= X0, |theta - 2*pi*x| >= eta |x| with
eta = 2*pi - theta_max/X0.  The order-r48 rung therefore gives each family
value <= D_i |x|^-48.  The four-factor polynomial obeys
|P(x)|^2 <= beta^8 |x|^8, beta = 2*pi + max_j |z_j|/X0.  A crude but explicit
digamma bound gives |sigma_arch(2*pi*x)| <= log |x| + C_sigma on this tail.
The remaining integral is elementary:

  integral_X0^infty (C0 + log x) x^-184 dx
    = X0^-183 * ((C0 + log X0)/183 + 1/183^2).
"""

from __future__ import annotations

import json
import math
import os
import sys
from pathlib import Path

import mpmath as mp
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import fourpoint_owner_completion_1980 as r80  # noqa: E402
import fourpoint_owner_density_1959 as r59  # noqa: E402
import routea_g8h_basis_comparison_2037 as r37  # noqa: E402

OUTPUT = ROOT / "results" / "2178_routea_infinity_algebraic_remainder.json"
K = mp.mpf(30)
R = 48
SAFETY = mp.mpf(100)
X0 = mp.mpf(1_000_000)
N48_UPPER = mp.mpf(
    json.loads(
        (ROOT / "results" / "2135_routea_root_partition_lipschitz.json").read_text(
            encoding="utf-8"
        )
    )["variation_upper"]
)


def main() -> None:
    mp.mp.dps = 100
    rho, nodes, values, fam, _xw, gram, _a, _, _ = r37.setup(False)
    xw = [r59.phi_weights(a, panels=6, m=6400) for a, _theta in fam]
    a_mat = r80.family_values(fam, float(K), np.asarray(nodes, complex), xw).T
    corr, solve_info = r37.min_h1(gram, a_mat, np.asarray(values, complex))
    base, _ = r37.min_h1(gram, a_mat, np.ones(len(nodes), complex))

    theta_max = mp.mpf(max(abs(float(theta)) for _a, theta in fam))
    eta = 2 * mp.pi - theta_max / X0
    counterpart = r80.counterpart_nodes(rho)
    node_radius = mp.mpf(max(abs(complex(z)) for z in counterpart))
    beta = 2 * mp.pi + node_radius / X0

    # The shifted Stirling expansion gives |sigma_arch(2*pi*x)| <= log(x)+10
    # for x >= 1e6.  The constant 10 deliberately absorbs log(pi), the eight
    # shift terms, the 1/(2w) term, all six Bernoulli terms and the remainder.
    C_SIGMA = mp.mpf(10)
    prime_powers = r59.rig.prime_powers_up_to(math.exp(9.504))
    c_book = mp.mpf(sum(2.0 * weight / math.sqrt(number)
                        for number, weight in prime_powers))
    C0 = c_book + 2 + C_SIGMA

    family_data = []
    for (a, _theta), bcoef, ccoef in zip(fam, base, corr):
        a_mp = mp.mpf(float(a))
        # v_bound(a,t) <= exp(a^2/2) * SAFETY*N48*a^(-(2R-2))
        #                       * (eta*x)^(-R)
        D = (mp.exp(a_mp * a_mp / 2) * SAFETY * N48_UPPER
             * a_mp ** (-(2 * R - 2)) * eta ** (-R))
        family_data.append((mp.mpf(abs(complex(bcoef))),
                            mp.mpf(abs(complex(ccoef))), D))

    B = sum(b * D for b, _c, D in family_data)
    C = sum(c * D for _b, c, D in family_data)
    q = 4 * R - 8  # x^8 from |P|^2 and x^(-4R) from four rungs
    power = q - 1
    integral_factor = X0 ** (-power) * ((C0 + mp.log(X0)) / power
                                        + mp.mpf(1) / power ** 2)
    one_side = beta ** 8 * B ** 2 * C ** 2 * integral_factor
    two_sided = 2 * one_side

    if not (eta > 0 and B >= 0 and C >= 0 and one_side >= 0):
        raise RuntimeError("algebraic tail constants failed basic positivity")

    result = {
        "record": 2178,
        "status": "INFINITY-TAIL-ALGEBRAIC-REMAINDER-BOUND-CANDIDATE",
        "consumer": "same-owner signed C3' tail, then SourceRH",
        "owner": "one-copy G8-H numerical owner (not complete closed-ball owner)",
        "rung": R,
        "x0": str(X0),
        "eta": mp.nstr(eta, 40),
        "beta": mp.nstr(beta, 40),
        "theta_max": mp.nstr(theta_max, 40),
        "node_radius": mp.nstr(node_radius, 40),
        "N48_upper_source": "results/2135_routea_root_partition_lipschitz.json",
        "C_sigma": str(C_SIGMA),
        "C_book": mp.nstr(c_book, 40),
        "C0": mp.nstr(C0, 40),
        "B_base": mp.nstr(B, 40),
        "B_correction": mp.nstr(C, 40),
        "integral_power": q,
        "one_sided_tail_bound": mp.nstr(one_side, 40),
        "two_sided_tail_bound": mp.nstr(two_sided, 40),
        "q1600_abs": "3.406049871881275e12",
        "l2_charge": "4.412215566637855e10",
        "two_sided_over_q1600": mp.nstr(two_sided / mp.mpf("3.406049871881275e12"), 40),
        "two_sided_over_l2": mp.nstr(two_sided / mp.mpf("4.412215566637855e10"), 40),
        "solve": solve_info,
        "checks": {
            "both_signs": True,
            "no_float_underflow_remainder": True,
            "closed_form_integral": True,
            "denominator_exponent": "|theta-2*pi*x| >= eta*|x|",
            "polynomial_modulus": "|P|^2 <= beta^8 |x|^8",
        },
        "nonclaims": [
            "N48 is still an mpmath interval candidate, not an independent Arb/Lean enclosure",
            "coefficient and Gram paths are stored-float owner measurements",
            "C_sigma is a deliberately broad elementary bound but its shifted-Stirling derivation is not yet formalized",
            "this closes only the algebraic infinity remainder for the one-copy numerical owner",
            "no complete-owner transfer, finite-window signed margin, producer theorem, or RH claim",
        ],
        "provenance": {
            "prior_screen": "results/2137_routea_fixed_r48_absP_screen.json",
            "variation_source": "results/2135_routea_root_partition_lipschitz.json",
            "owner_source": "results/2058_l5_solve.json",
            "script": os.fspath(Path(__file__).relative_to(ROOT)),
        },
    }
    OUTPUT.write_text(json.dumps(result, indent=2, default=str) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2, default=str))


if __name__ == "__main__":
    main()
