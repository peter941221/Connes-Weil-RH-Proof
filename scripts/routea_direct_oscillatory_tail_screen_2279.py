"""2279: direct composite Gauss-Legendre oscillatory tail screen.

Unlike record 2278, this changes the quadrature rule instead of refining one
FFT class. It integrates the corrected physical owner directly and uses the
support-derived signed kernel. It remains a screen, not a certificate.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path
import sys

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import fourpoint_diagonal_sign_1918 as rig
CAPTURE = ROOT / "results/2275_gap_owner_audit.json"
OUT = ROOT / "results/2279_direct_oscillatory_tail_screen.json"
K = 30.0
GAMMA = 39.25244858548658
DELTA = 0.445

def load_owner():
    capture = json.loads(CAPTURE.read_text())
    owner = capture["owner_capture"]
    families = [(float.fromhex(width), float.fromhex(theta)) for width, theta in owner["families_hex"]]
    base = np.array([complex(float.fromhex(real), float.fromhex(imag)) for real, imag in owner["base_hex"]])
    corr = np.array([complex(float.fromhex(real), float.fromhex(imag)) for real, imag in owner["corr_hex"]])
    return capture, families, base, corr

def quadrature_nodes(half_width, panels, order):
    legendre, weights = np.polynomial.legendre.leggauss(order)
    points = []
    masses = []
    edges = np.linspace(-half_width, half_width, panels + 1)
    for left, right in zip(edges[:-1], edges[1:]):
        points.append(0.5 * (right - left) * legendre + 0.5 * (left + right))
        masses.append(0.5 * (right - left) * weights)
    return np.concatenate(points), np.concatenate(masses)

def owner_values(y, families, coefficients):
    values = np.zeros_like(y, dtype=complex)
    for coefficient, (width, theta) in zip(coefficients, families):
        radius = width * width
        q = 1.0 - (y / radius) ** 2
        phi = np.zeros_like(y)
        mask = q > 0.0
        phi[mask] = np.exp(-K / q[mask])
        values += coefficient * phi * np.exp((0.5 + 1j * theta) * y)
    return values

def transforms(xi, y, weights, families, coefficients):
    values = owner_values(y, families, coefficients) * weights
    output = np.empty(xi.shape, dtype=complex)
    for lo in range(0, xi.size, 256):
        hi = min(lo + 256, xi.size)
        output[lo:hi] = np.exp(-2j * np.pi * xi[lo:hi, None] * y[None, :]) @ values
    return output

def prime_kernel(xi, support):
    primes = rig.prime_powers_up_to(math.exp(support))
    kernel = rig.sigma_vec(2.0 * np.pi * xi).astype(float)
    logn = np.asarray([math.log(number) for number, _ in primes])
    weights = np.asarray([weight / math.sqrt(number) for number, weight in primes])
    for lo in range(0, len(logn), 256):
        hi = lo + 256
        kernel += 2.0 * np.sum(weights[lo:hi, None] * np.cos(2.0 * np.pi * logn[lo:hi, None] * xi[None, :]), axis=0)
    return kernel, len(primes)

def annihilator(xi):
    rho = (0.5 + DELTA) + 1j * GAMMA
    nodes = [rho - 0.5, (1 - np.conj(rho)) - 0.5, np.conj(rho) - 0.5, (1 - rho) - 0.5]
    polynomial = np.ones_like(xi, dtype=complex)
    s = -2j * np.pi * xi
    for node in nodes:
        polynomial *= node - s
    return polynomial

def run(order, xi_max, xi_step, panels=6):
    capture, families, base, corr = load_owner()
    half_width = max(width * width for width, _ in families)
    support = 2.0 * half_width
    y, weights = quadrature_nodes(half_width, panels, order)
    xi = np.arange(40.0, xi_max + xi_step / 2.0, xi_step)
    base_transform = transforms(xi, y, weights, families, base)
    corr_transform = transforms(xi, y, weights, families, corr)
    kernel, prime_count = prime_kernel(xi, support)
    integrand = kernel * np.abs(annihilator(xi)) ** 2 * np.abs(base_transform) ** 2 * np.abs(corr_transform) ** 2
    return {"order": order, "panels": panels, "xi_max": xi_max, "xi_step": xi_step,
            "quadrature_nodes": int(y.size), "support_half_width": half_width,
            "prime_power_count": prime_count, "xi_points": int(xi.size),
            "signed_integral": float(np.trapezoid(integrand, xi)),
            "absolute_integral": float(np.trapezoid(np.abs(integrand), xi)),
            "negative_absolute_mass": float(np.trapezoid(np.maximum(-integrand, 0.0), xi)),
            "base_transform_max": float(np.max(np.abs(base_transform))),
            "corr_transform_max": float(np.max(np.abs(corr_transform))),
            "base_md5": capture["owner_capture"]["base_md5"], "corr_md5": capture["owner_capture"]["corr_md5"]}

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--xi-max", type=float, default=200.0)
    parser.add_argument("--xi-step", type=float, default=0.25)
    parser.add_argument("--orders", default="64,128,256")
    parser.add_argument("--output", type=Path, default=OUT)
    args = parser.parse_args()
    readings = [run(int(order), args.xi_max, args.xi_step) for order in args.orders.split(",")]
    result = {"record": 2279, "status": "DIRECT-OSCILLATORY-SCREEN", "certificate": False, "hgap_closed": False,
              "readings": readings,
              "input_sha256": {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest() for path in (CAPTURE,)},
              "nonclaims": ["finite xi range is not the infinite tail", "floating quadrature is not a directed enclosure", "no selected-detector readback", "no hgap supplier, producer GO or RH claim"]}
    base = readings[0]
    result["order_refinement"] = [{"from": readings[index]["order"], "to": readings[index + 1]["order"], "signed_relative_change": abs(readings[index + 1]["signed_integral"] - readings[index]["signed_integral"]) / max(abs(readings[index + 1]["signed_integral"]), 1e-300), "absolute_relative_change": abs(readings[index + 1]["absolute_integral"] - readings[index]["absolute_integral"]) / max(abs(readings[index + 1]["absolute_integral"]), 1e-300)} for index in range(len(readings) - 1)]
    result["trust_status"] = ("DIRECT-GL-TAIL-UNTRUSTED"
                               if max(max(row["signed_relative_change"], row["absolute_relative_change"])
                                      for row in result["order_refinement"]) > 1e-3
                               else "DIRECT-GL-REFINEMENT-STABLE")
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print("DIRECT-OSCILLATORY-SCREEN")
    print(json.dumps({"signed": base["signed_integral"], "absolute": base["absolute_integral"], "prime_power_count": base["prime_power_count"]}))

if __name__ == "__main__":
    main()
