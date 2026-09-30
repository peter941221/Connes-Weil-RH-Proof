"""2278: signed-kernel oscillatory tail screen for the corrected owner.

This probe uses the corrected width-a^2 physical profiles, FFT Laplace
transforms, and the support-derived visible prime-power kernel. It is a
finite-range numerical screen only; it is not an analytic tail certificate.
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
OUT = ROOT / "results/2278_signed_kernel_tail_screen.json"
K = 30.0
GAMMA = 39.25244858548658
DELTA = 0.445

def load_owner():
    capture = json.loads(CAPTURE.read_text())
    owner = capture["owner_capture"]
    families = [(float.fromhex(width), float.fromhex(theta))
                for width, theta in owner["families_hex"]]
    base = np.array([complex(float.fromhex(real), float.fromhex(imag))
                     for real, imag in owner["base_hex"]])
    corr = np.array([complex(float.fromhex(real), float.fromhex(imag))
                     for real, imag in owner["corr_hex"]])
    return capture, families, base, corr

def physical_fields(y, families, coefficients, sigma=0.5):
    value = np.zeros(y.shape, dtype=complex)
    for coefficient, (width, theta) in zip(coefficients, families):
        radius = width * width
        u = y / radius
        q = 1.0 - u * u
        mask = q > 0.0
        phi = np.zeros_like(y)
        phi[mask] = np.exp(-K / q[mask])
        value += coefficient * phi * np.exp(sigma * y + 1j * theta * y)
    return value

def fft_laplace(values, dy, y0):
    frequency = np.fft.fftfreq(values.size, d=dy)
    transform = np.fft.fft(values) * dy * np.exp(-2j * np.pi * frequency * y0)
    order = np.argsort(frequency)
    return frequency[order], transform[order]

def prime_kernel(xi, support):
    primes = rig.prime_powers_up_to(math.exp(support))
    kernel = rig.sigma_vec(2.0 * np.pi * xi).astype(float)
    logn = np.asarray([math.log(number) for number, _ in primes])
    weights = np.asarray([weight / math.sqrt(number) for number, weight in primes])
    chunk = 256
    for lo in range(0, len(logn), chunk):
        kernel += 2.0 * np.sum(weights[lo:lo + chunk, None] *
                                 np.cos(2.0 * np.pi * logn[lo:lo + chunk, None] * xi[None, :]), axis=0)
    return kernel, len(primes)

def annihilator(xi):
    rho = (0.5 + DELTA) + 1j * GAMMA
    nodes = [rho - 0.5, (1 - np.conj(rho)) - 0.5,
             np.conj(rho) - 0.5, (1 - rho) - 0.5]
    s = -2j * np.pi * xi
    polynomial = np.ones_like(s, dtype=complex)
    for node in nodes:
        polynomial *= node - s
    return polynomial

def run(nodes, xi_max):
    capture, families, base, corr = load_owner()
    max_radius = max(width * width for width, _ in families)
    support = 2.0 * max_radius
    y = np.linspace(-max_radius, max_radius, nodes, endpoint=False)
    dy = float(y[1] - y[0])
    base_values = physical_fields(y, families, base)
    corr_values = physical_fields(y, families, corr)
    frequency, base_transform = fft_laplace(base_values, dy, float(y[0]))
    _, corr_transform = fft_laplace(corr_values, dy, float(y[0]))
    mask = (frequency >= 40.0) & (frequency <= xi_max)
    xi = frequency[mask]
    kernel, prime_count = prime_kernel(xi, support)
    polynomial = annihilator(xi)
    integrand = kernel * np.abs(polynomial) ** 2 * np.abs(base_transform[mask]) ** 2 * np.abs(corr_transform[mask]) ** 2
    positive = integrand >= 0
    integral = float(np.trapezoid(integrand[positive], xi[positive]))
    negative_mass = float(np.trapezoid(np.abs(integrand[integrand < 0]), xi[integrand < 0]))
    absolute = float(np.trapezoid(np.abs(integrand), xi))
    return {"nodes": nodes, "xi_max": xi_max, "dy": dy,
            "frequency_step": float(frequency[1] - frequency[0]),
            "support_half_width": max_radius, "convolution_support": support,
            "prime_power_count": prime_count, "xi_points": int(xi.size),
            "signed_integral_40_to_xi_max": integral,
            "negative_absolute_mass": negative_mass,
            "absolute_integral_40_to_xi_max": absolute,
            "signed_to_absolute_ratio": integral / absolute if absolute else 0.0,
            "base_md5": capture["owner_capture"]["base_md5"],
            "corr_md5": capture["owner_capture"]["corr_md5"]}

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--nodes", type=int, default=262144)
    parser.add_argument("--xi-max", type=float, default=500.0)
    parser.add_argument("--refine", action="store_true")
    parser.add_argument("--output", type=Path, default=OUT)
    args = parser.parse_args()
    coarse = run(args.nodes, args.xi_max)
    result = {"record": 2278, "status": "SIGNED-KERNEL-OSCILLATORY-SCREEN",
              "certificate": False, "hgap_closed": False,
              "screen": coarse,
              "nonclaims": ["finite FFT range is not the infinite tail",
                            "FFT values are not directed enclosures",
                            "no selected-detector readback",
                            "no hgap supplier, producer GO or RH claim"],
              "input_sha256": {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
                               for path in (CAPTURE,)}}
    if args.refine:
        fine = run(args.nodes * 2, args.xi_max)
        signed_change = abs(fine["signed_integral_40_to_xi_max"] - coarse["signed_integral_40_to_xi_max"]) / max(abs(fine["signed_integral_40_to_xi_max"]), 1e-300)
        absolute_change = abs(fine["absolute_integral_40_to_xi_max"] - coarse["absolute_integral_40_to_xi_max"]) / max(abs(fine["absolute_integral_40_to_xi_max"]), 1e-300)
        result["refinement"] = {"coarse": coarse, "fine": fine,
                                "signed_relative_change": signed_change,
                                "absolute_relative_change": absolute_change,
                                "trust_status": "FFT-TAIL-UNTRUSTED" if max(signed_change, absolute_change) > 1e-3 else "FFT-REFINEMENT-STABLE"}
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print("SIGNED-KERNEL-OSCILLATORY-SCREEN")
    print(json.dumps({"signed": coarse["signed_integral_40_to_xi_max"], "absolute": coarse["absolute_integral_40_to_xi_max"], "primes": coarse["prime_power_count"]}))

if __name__ == "__main__":
    main()
