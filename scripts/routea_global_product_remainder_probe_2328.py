"""Record 2328: product-derivative majorant for the GL remainder.

This constructs a global, intentionally conservative derivative majorant for
W = |P|^2 |L_base|^2 |L_corr|^2 and inserts it into the GL16 remainder
formula. It is a feasibility probe: sampled polynomial maxima and stored
float coefficients are not yet a formal enclosure.
"""
import importlib
import json
import math
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
r2249 = importlib.import_module("routea_weighted_zero_l1_enclosure_2249")
e2308 = importlib.import_module("routea_hgap_window_cert_2308")


def conv_derivative(left, right, order):
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
    basis_base = np.zeros(order + 1)
    basis_corr = np.zeros(order + 1)
    for index, (width, _theta) in enumerate(families):
        X, f, _ef = r2249.phi_terms(width, xw[index])
        envelope = np.abs(f) * np.exp(0.5 * width * X) * width
        scale = 2.0 * np.pi * width * np.abs(X)
        for derivative in range(order + 1):
            moment = float(np.sum(envelope * scale ** derivative))
            basis_base[derivative] += abs(base[index]) * moment
            basis_corr[derivative] += abs(correction[index]) * moment
    base_square = conv_derivative(basis_base, basis_base, order)
    corr_square = conv_derivative(basis_corr, basis_corr, order)

    poly = np.poly1d([1.0 + 0.0j])
    for root in r2249.r80.counterpart_nodes(rho):
        poly = np.polymul(poly, np.poly1d([-2j * np.pi, -root]))
    grid = np.linspace(-40.0, 40.0, 40001)
    poly_derivative = np.zeros(order + 1)
    for derivative in range(order + 1):
        value = np.polyval(np.polyder(poly, derivative), grid)
        poly_derivative[derivative] = float(np.max(np.abs(np.real(value))))
    p_square = conv_derivative(poly_derivative, poly_derivative, order)
    owner_derivative = conv_derivative(
        conv_derivative(p_square, base_square, order), corr_square, order
    )

    carrier = e2308.evaluator.bridge.refined.remainder.carrier
    source = carrier.SOURCE
    primes = source.rig.prime_powers_up_to(
        math.exp(2.0 * max(width * width for width, _ in families))
    )
    numbers = np.asarray([number for number, _ in primes], dtype=float)
    lam = np.asarray([weight for _, weight in primes], dtype=float)
    mask = numbers > 167
    numbers, lam = numbers[mask], lam[mask]
    phi = 2.0 * np.pi * np.log(numbers)
    remainder_prefactor = (0.25 ** 33 * math.factorial(16) ** 4
                           / (33 * math.factorial(32) ** 3))
    derivative_order = 32
    weighted_remainder = 0.0
    for frequency, weight in zip(phi, 2.0 * lam / np.sqrt(numbers)):
        derivative_bound = sum(
            math.comb(derivative_order, k)
            * owner_derivative[k]
            * frequency ** (derivative_order - k)
            for k in range(derivative_order + 1)
        )
        weighted_remainder += weight * remainder_prefactor * derivative_bound
    result = {
        "record": 2328,
        "derivative_order": derivative_order,
        "panel_width": 0.25,
        "prime_count": int(numbers.size),
        "owner_weight_derivative_0": float(owner_derivative[0]),
        "owner_weight_derivative_32": float(owner_derivative[32]),
        "gl_product_remainder_majorant": float(weighted_remainder),
        "remainder_over_margin": float(weighted_remainder / 1.675396046388e12),
        "status": "GLOBAL_PRODUCT_MAJORANT_PROBE_NOT_CERTIFICATE",
        "caveats": ["sampled polynomial derivative maxima", "stored float coefficient bounds", "global rather than panel-local majorant"],
    }
    out = ROOT / "results" / "2328_global_product_remainder_probe.json"
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
