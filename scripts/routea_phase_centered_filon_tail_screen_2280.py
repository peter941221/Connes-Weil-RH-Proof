"""2280: phase-centred local Chebyshev-Filon tail screen."""
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
OUT = ROOT / "results/2280_phase_centered_filon_tail_screen.json"
K = 30.0
GAMMA = 39.25244858548658
DELTA = 0.445

def load_owner():
    capture = json.loads(CAPTURE.read_text())
    owner = capture["owner_capture"]
    families = [(float.fromhex(a), float.fromhex(b)) for a, b in owner["families_hex"]]
    base = np.array([complex(float.fromhex(a), float.fromhex(b)) for a, b in owner["base_hex"]])
    corr = np.array([complex(float.fromhex(a), float.fromhex(b)) for a, b in owner["corr_hex"]])
    return capture, families, base, corr

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

def polynomial_moments(alpha, degree):
    moments = np.empty(degree + 1, dtype=complex)
    if abs(alpha) < 1e-12:
        for index in range(degree + 1):
            moments[index] = 2.0 / (index + 1) if index % 2 == 0 else 0.0
        return moments
    moments[0] = 2.0 * math.sin(alpha) / alpha
    minus = complex(math.cos(alpha), -math.sin(alpha))
    plus = complex(math.cos(alpha), math.sin(alpha))
    for index in range(1, degree + 1):
        boundary = minus - ((-1) ** index) * plus
        moments[index] = (index * moments[index - 1] - boundary) / (1j * alpha)
    return moments

def filon_transform(xi, families, coefficients, panels, degree):
    half_width = max(width * width for width, _ in families)
    edges = np.linspace(-half_width, half_width, panels + 1)
    cheb_nodes = np.cos(np.pi * np.arange(degree + 1) / degree)
    output = np.zeros_like(xi, dtype=complex)
    for left, right in zip(edges[:-1], edges[1:]):
        centre = 0.5 * (left + right)
        half = 0.5 * (right - left)
        y_nodes = centre + half * cheb_nodes
        amplitude = owner_values(y_nodes, families, coefficients)
        power_coefficients = np.polynomial.chebyshev.cheb2poly(np.polynomial.chebyshev.chebfit(cheb_nodes, amplitude, degree))
        for index, frequency in enumerate(xi):
            alpha = 2.0 * np.pi * frequency * half
            moments = polynomial_moments(alpha, degree)
            phase = complex(math.cos(-2.0 * np.pi * frequency * centre), math.sin(-2.0 * np.pi * frequency * centre))
            output[index] += half * phase * np.dot(power_coefficients, moments)
    return output

def prime_kernel(xi, support):
    primes = rig.prime_powers_up_to(math.exp(support))
    kernel = rig.sigma_vec(2.0 * np.pi * xi).astype(float)
    logn = np.asarray([math.log(number) for number, _ in primes])
    weights = np.asarray([weight / math.sqrt(number) for number, weight in primes])
    for lo in range(0, len(logn), 256):
        hi = min(lo + 256, len(logn))
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

def run(panels, degree, xi_max, xi_step):
    capture, families, base, corr = load_owner()
    half_width = max(width * width for width, _ in families)
    xi = np.arange(40.0, xi_max + xi_step / 2.0, xi_step)
    base_transform = filon_transform(xi, families, base, panels, degree)
    corr_transform = filon_transform(xi, families, corr, panels, degree)
    kernel, prime_count = prime_kernel(xi, 2.0 * half_width)
    integrand = kernel * np.abs(annihilator(xi)) ** 2 * np.abs(base_transform) ** 2 * np.abs(corr_transform) ** 2
    return {"panels": panels, "degree": degree, "xi_max": xi_max, "xi_step": xi_step, "xi_points": int(xi.size), "support_half_width": half_width, "prime_power_count": prime_count, "signed_integral": float(np.trapezoid(integrand, xi)), "absolute_integral": float(np.trapezoid(np.abs(integrand), xi)), "negative_absolute_mass": float(np.trapezoid(np.maximum(-integrand, 0.0), xi)), "base_transform_max": float(np.max(np.abs(base_transform))), "corr_transform_max": float(np.max(np.abs(corr_transform))), "base_md5": capture["owner_capture"]["base_md5"], "corr_md5": capture["owner_capture"]["corr_md5"]}

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--xi-max", type=float, default=200.0)
    parser.add_argument("--xi-step", type=float, default=0.25)
    parser.add_argument("--profiles", default="12:12,18:16,24:20")
    parser.add_argument("--output", type=Path, default=OUT)
    args = parser.parse_args()
    readings = [run(int(p), int(d), args.xi_max, args.xi_step) for p, d in (item.split(":") for item in args.profiles.split(","))]
    result = {"record": 2280, "status": "PHASE-CENTERED-FILON-SCREEN", "certificate": False, "hgap_closed": False, "readings": readings, "input_sha256": {str(CAPTURE.relative_to(ROOT)): hashlib.sha256(CAPTURE.read_bytes()).hexdigest()}, "nonclaims": ["finite xi range is not the infinite tail", "polynomial interpolation is not an interval enclosure", "no selected-detector readback", "no hgap supplier, producer GO or RH claim"]}
    result["profile_refinement"] = [{"from": readings[i]["degree"], "to": readings[i + 1]["degree"], "signed_relative_change": abs(readings[i + 1]["signed_integral"] - readings[i]["signed_integral"]) / max(abs(readings[i + 1]["signed_integral"]), 1e-300), "absolute_relative_change": abs(readings[i + 1]["absolute_integral"] - readings[i]["absolute_integral"]) / max(abs(readings[i + 1]["absolute_integral"]), 1e-300)} for i in range(len(readings) - 1)]
    worst = max(max(row["signed_relative_change"], row["absolute_relative_change"]) for row in result["profile_refinement"])
    result["trust_status"] = "FILON-PROFILE-UNTRUSTED" if worst > 1e-3 else "FILON-PROFILE-STABLE-SCREEN"
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(result["trust_status"])
    print(json.dumps({"signed": readings[0]["signed_integral"], "absolute": readings[0]["absolute_integral"], "prime_power_count": readings[0]["prime_power_count"]}))

if __name__ == "__main__":
    main()
