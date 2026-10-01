"""Record 2332: panel-local Taylor enclosure feasibility.

For each panel, owner coefficients are combined in center derivatives. A local
Taylor polynomial is then inflated by an order-34 absolute basis tail. This is
still a floating diagnostic, but unlike endpoint sampling it has an explicit
Taylor-radius mechanism.
"""
import importlib
import json
import math
import sys
from pathlib import Path

import numpy as np
import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
r2249 = importlib.import_module("routea_weighted_zero_l1_enclosure_2249")
e2308 = importlib.import_module("routea_hgap_window_cert_2308")


def product_sup(left, right, order):
    return np.asarray([
        sum(math.comb(j, k) * left[k] * right[j - k]
            for k in range(j + 1))
        for j in range(order + 1)
    ], dtype=float)


def main():
    rho, nodes, values, families = r2249.build()
    xw_cache = {}
    xw = []
    for width, _ in families:
        if float(width) not in xw_cache:
            xw_cache[float(width)] = r2249.phi_weights_cached(width)
        xw.append(xw_cache[float(width)])
    matrix = r2249.r80.family_values(
        families, r2249.K, np.asarray(nodes, complex), xw
    ).T
    base = np.linalg.solve(matrix, np.ones(len(nodes), complex))
    correction = np.linalg.solve(matrix, np.asarray(values, complex))
    order = 32
    tail_order = 34
    radius = 0.125
    edges = np.linspace(-40.0, 40.0, 321)
    centers = 0.5 * (edges[:-1] + edges[1:])
    p_poly = np.poly1d([1.0 + 0.0j])
    for root in r2249.r80.counterpart_nodes(rho):
        p_poly = np.polymul(p_poly, np.poly1d([-2j * np.pi, -root]))
    p_center_sup = []
    remainder_proxies = []
    for center in centers:
        base_center = np.zeros(tail_order + 1, dtype=complex)
        corr_center = np.zeros(tail_order + 1, dtype=complex)
        base_abs_tail = 0.0
        corr_abs_tail = 0.0
        for index, (width, theta) in enumerate(families):
            X, f, _ef = r2249.phi_terms(width, xw[index])
            phase = np.exp(0.5 * width * X
                           + 1j * width * (theta - 2.0 * np.pi * center) * X)
            seed = width * f * phase
            step = -2j * np.pi * width * X
            power = np.ones_like(step, dtype=complex)
            abs_power = np.abs(step) ** tail_order
            mp.iv.dps = 80
            basis_tail_iv = mp.iv.mpf(0)
            for f_value, x_value in zip(f, X):
                f_iv = mp.iv.mpf(float(abs(f_value)))
                exp_iv = mp.iv.exp(mp.iv.mpf(float(0.5 * width * x_value)))
                scale_iv = mp.iv.mpf(float(2.0 * np.pi * width * abs(x_value)))
                basis_tail_iv += f_iv * exp_iv * mp.iv.mpf(float(width)) * scale_iv ** tail_order
            basis_tail = float(basis_tail_iv.b)
            base_abs_tail += abs(base[index]) * basis_tail
            corr_abs_tail += abs(correction[index]) * basis_tail
            for derivative in range(tail_order + 1):
                value = np.sum(seed * power)
                base_center[derivative] += base[index] * value
                corr_center[derivative] += correction[index] * value
                power *= step
        base_sup = np.zeros(order + 1)
        corr_sup = np.zeros(order + 1)
        for derivative in range(order + 1):
            base_sup[derivative] = sum(
                abs(base_center[derivative + j]) * radius ** j / math.factorial(j)
                for j in range(tail_order - derivative)
            ) + base_abs_tail * radius ** (tail_order - derivative) / math.factorial(tail_order - derivative)
            corr_sup[derivative] = sum(
                abs(corr_center[derivative + j]) * radius ** j / math.factorial(j)
                for j in range(tail_order - derivative)
            ) + corr_abs_tail * radius ** (tail_order - derivative) / math.factorial(tail_order - derivative)
        base_square = product_sup(base_sup, base_sup, order)
        corr_square = product_sup(corr_sup, corr_sup, order)
        p_sup = np.zeros(order + 1)
        for derivative in range(5):
            p_center = np.polyval(np.polyder(p_poly, derivative), center).real
            p_sup[derivative] = sum(
                abs(np.polyval(np.polyder(p_poly, derivative + j), center).real)
                * radius ** j / math.factorial(j)
                for j in range(5 - derivative)
            )
        p_square = product_sup(p_sup, p_sup, order)
        weight_sup = product_sup(product_sup(p_square, base_square, order), corr_square, order)
        remainder_proxies.append(weight_sup)
    weight_max_by_order = np.max(np.asarray(remainder_proxies), axis=0)
    carrier = e2308.evaluator.bridge.refined.remainder.carrier
    source = carrier.SOURCE
    primes = source.rig.prime_powers_up_to(
        math.exp(2.0 * max(width * width for width, _ in families))
    )
    numbers = np.asarray([number for number, _ in primes], dtype=float)
    lam = np.asarray([value for _, value in primes], dtype=float)
    mask = numbers > 167
    numbers, lam = numbers[mask], lam[mask]
    phi = 2.0 * np.pi * np.log(numbers)
    weighted = 2.0 * lam / np.sqrt(numbers)
    prefactor = 0.25 ** 33 * math.factorial(16) ** 4 / (33 * math.factorial(32) ** 3)
    terms = [
        math.comb(32, derivative) * weight_max_by_order[derivative]
        * float(np.sum(weighted * phi ** (32 - derivative)))
        for derivative in range(33)
    ]
    remainder = prefactor * float(np.sum(terms))
    result = {
        "record": 2333,
        "panel_count": len(centers),
        "panel_width": 0.25,
        "radius": radius,
        "tail_order": tail_order,
        "weight_sup_order32": float(weight_max_by_order[32]),
        "local_taylor_remainder_proxy": remainder,
        "proxy_over_margin": remainder / 1.675396046388e12,
        "status": "DIRECTED_TAIL_DIAGNOSTIC_NOT_CERTIFICATE",
        "caveats": ["stored float arithmetic", "absolute tail uses basis triangle", "no directed interval implementation"],
    }
    out = ROOT / "results" / "2333_directed_tail_probe.json"
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
