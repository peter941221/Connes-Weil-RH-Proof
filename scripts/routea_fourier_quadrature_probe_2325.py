"""Record 2325: independent Gauss-Legendre Fourier coefficient probe.

The probe evaluates the same selected owner at composite Gauss-Legendre orders
8 and 16 on the same panels. The order-difference is an empirical quadrature
control only; it is not a remainder theorem.
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


def owner_setup():
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
    return rho, families, xw, base, correction


def owner_weight(points, rho, families, xw, base, correction):
    values = r2249.r80.family_values(
        families, r2249.K, 0.5 - 2j * np.pi * points, xw
    )
    base_laplace = base @ values
    correction_laplace = correction @ values
    annihilator = np.real(r2249.r59.P_from_nodes(
        points, r2249.r80.counterpart_nodes(rho)
    ))
    return (annihilator * annihilator
            * np.abs(base_laplace) ** 2
            * np.abs(correction_laplace) ** 2)


def coefficients(order, panels, prime_numbers, prime_lam, rho, families, xw,
                 base, correction):
    legendre_x, legendre_w = np.polynomial.legendre.leggauss(order)
    edges = np.linspace(-40.0, 40.0, panels + 1)
    points = []
    weights = []
    for left, right in zip(edges[:-1], edges[1:]):
        points.append(0.5 * (right - left) * legendre_x + 0.5 * (left + right))
        weights.append(0.5 * (right - left) * legendre_w)
    points = np.concatenate(points)
    weights = np.concatenate(weights)
    owner = owner_weight(points, rho, families, xw, base, correction)
    phi = 2.0 * np.pi * np.log(prime_numbers.astype(float))
    result = np.empty(phi.size, dtype=float)
    for start in range(0, phi.size, 256):
        stop = min(start + 256, phi.size)
        phase = phi[start:stop, None] * points[None, :]
        result[start:stop] = (2.0 * prime_lam[start:stop]
                              / np.sqrt(prime_numbers[start:stop])
                              * np.sum(np.cos(phase) * (owner * weights)[None, :], axis=1))
    return result, float(np.sum(result)), float(np.sum(np.abs(result)))


def main():
    rho, families, xw, base, correction = owner_setup()
    carrier = e2308.evaluator.bridge.refined.remainder.carrier
    source = carrier.SOURCE
    primes = source.rig.prime_powers_up_to(
        math.exp(2.0 * max(width * width for width, _ in families))
    )
    numbers = np.asarray([number for number, _ in primes], dtype=np.int64)
    lam = np.asarray([weight for _, weight in primes], dtype=float)
    mask = numbers > 167
    numbers = numbers[mask]
    lam = lam[mask]
    runs = {}
    for order, panels in ((8, 160), (16, 160), (16, 320), (16, 640)):
        values, signed, abs_sum = coefficients(
            order, panels, numbers, lam, rho, families, xw, base, correction
        )
        runs[f"gl{order}_p{panels}"] = {
            "signed": signed,
            "abs_sum": abs_sum,
            "count": int(values.size),
        }
        if order == 16 and panels == 160:
            reference = values
        if order == 8 and panels == 160:
            gl8 = values
        if order == 16 and panels == 320:
            fine = values
        if order == 16 and panels == 640:
            ultra = values
    result = {
        "record": 2325,
        "prime_count": int(numbers.size),
        "runs": runs,
        "gl16_p160_minus_gl8_p160_signed": float(np.sum(reference - gl8)),
        "gl16_p160_minus_gl8_p160_abs_sum": float(np.sum(np.abs(reference - gl8))),
        "gl16_p320_minus_gl16_p160_signed": float(np.sum(fine - reference)),
        "gl16_p320_minus_gl16_p160_abs_sum": float(np.sum(np.abs(fine - reference))),
        "gl16_p640_minus_gl16_p320_signed": float(np.sum(ultra - fine)),
        "gl16_p640_minus_gl16_p320_abs_sum": float(np.sum(np.abs(ultra - fine))),
        "status": "INDEPENDENT_QUADRATURE_DIAGNOSTIC_NOT_CERTIFICATE",
    }
    out = ROOT / "results" / "2325_fourier_quadrature_probe.json"
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
