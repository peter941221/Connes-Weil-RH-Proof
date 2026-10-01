"""Record 2329: panel-local cancellation-preserving derivative jets.

At each panel center, basis derivatives are combined with the selected owner
coefficients before absolute values are taken. The resulting local jets are a
feasibility diagnostic for the GL remainder; panel variation and interval
radii are deliberately not yet enclosed.
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


def product_jet(left, right, order):
    return np.asarray([
        sum(math.comb(j, k) * left[k] * right[j - k]
            for k in range(j + 1))
        for j in range(order + 1)
    ], dtype=complex)


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
    order = 33
    edges = np.linspace(-40.0, 40.0, 321)
    centers = 0.5 * (edges[:-1] + edges[1:])
    sample_points = np.concatenate([edges, centers])
    local_remainders = []
    local_derivative32 = []
    for center in sample_points:
        base_jet = np.zeros(order + 1, dtype=complex)
        corr_jet = np.zeros(order + 1, dtype=complex)
        for index, (width, theta) in enumerate(families):
            X, f, _ef = r2249.phi_terms(width, xw[index])
            phase = np.exp(0.5 * width * X
                           + 1j * width * (theta - 2.0 * np.pi * center) * X)
            seed = width * f * phase
            step = -2j * np.pi * width * X
            power = np.ones_like(step, dtype=complex)
            for derivative in range(order + 1):
                value = np.sum(seed * power)
                base_jet[derivative] += base[index] * value
                corr_jet[derivative] += correction[index] * value
                power *= step
        p_poly = np.poly1d([1.0 + 0.0j])
        for root in r2249.r80.counterpart_nodes(rho):
            p_poly = np.polymul(p_poly, np.poly1d([-2j * np.pi, -root]))
        p_jet = np.asarray([
            np.polyval(np.polyder(p_poly, derivative), center).real
            for derivative in range(order + 1)
        ], dtype=complex)
        weight_jet = product_jet(
            product_jet(p_jet, p_jet, order),
            product_jet(base_jet, np.conjugate(base_jet), order),
            order,
        )
        weight_jet = product_jet(
            weight_jet,
            product_jet(corr_jet, np.conjugate(corr_jet), order),
            order,
        )
        local_derivative32.append(abs(weight_jet[order]))
        local_remainders.append(weight_jet)

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
    remainder_order = 32
    prefactor = (0.25 ** 33 * math.factorial(16) ** 4 / (33 * math.factorial(32) ** 3))
    local_jets = np.asarray(local_remainders)
    local_max_by_order = np.max(np.abs(local_jets), axis=0)
    half_width = 0.125
    inflated = local_max_by_order[:remainder_order + 1] + half_width * local_max_by_order[1:remainder_order + 2]
    weighted_coefficients = 2.0 * lam / np.sqrt(numbers)
    local_remainder_terms = []
    for derivative in range(remainder_order + 1):
        frequency_power = remainder_order - derivative
        local_remainder_terms.append(float(math.comb(remainder_order, derivative) * inflated[derivative] * np.sum(weighted_coefficients * phi ** frequency_power)))
    local_remainder_full = prefactor * float(np.sum(local_remainder_terms))
    local_max = float(max(local_derivative32))
    local_mean = float(np.mean(local_derivative32))
    local_mean = float(np.mean(local_derivative32))
    frequency_sum = float(np.sum(2.0 * lam / np.sqrt(numbers) * phi ** 0))
    local_remainder_proxy = local_remainder_full
    result = {
        "record": 2331,
        "panel_count": len(centers),
        "sample_point_count": len(sample_points),
        "panel_width": 0.25,
        "derivative_order": order,
        "local_weight_derivative32_max": local_max,
        "local_weight_derivative32_mean": local_mean,
        "local_remainder_proxy": local_remainder_proxy,
        "proxy_over_margin": local_remainder_proxy / 1.675396046388e12,
        "global_probe_remainder": 9.235602894507e23,
        "status": "PANEL_LIPSCHITZ_DIAGNOSTIC_NOT_CERTIFICATE",
        "caveats": ["center and endpoint samples only", "no certified panel interval radius", "frequency product bound is intentionally crude"],
    }
    out = ROOT / "results" / "2331_panel_lipschitz_inflation.json"
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
