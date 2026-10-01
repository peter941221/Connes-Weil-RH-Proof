"""Record 2327: GL16 cosine-only remainder headroom.

This probe evaluates the Gauss-Legendre remainder prefactor and the termwise
cosine derivative contribution. It deliberately excludes derivatives of the
selected-owner weight W(xi); therefore it is a partial budget, not a
certificate.
"""
import importlib
import json
import math
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
probe = importlib.import_module("routea_fourier_quadrature_probe_2325")
e2308 = importlib.import_module("routea_hgap_window_cert_2308")

rho, families, xw, base, correction = probe.owner_setup()
points = np.linspace(-40.0, 40.0, 4001)
weight = probe.owner_weight(points, rho, families, xw, base, correction)
weight_max = float(np.max(weight))
carrier = e2308.evaluator.bridge.refined.remainder.carrier
source = carrier.SOURCE
primes = source.rig.prime_powers_up_to(
    math.exp(2.0 * max(width * width for width, _ in families))
)
numbers = np.asarray([number for number, _ in primes], dtype=np.float64)
lam = np.asarray([value for _, value in primes], dtype=np.float64)
mask = numbers > 167
numbers, lam = numbers[mask], lam[mask]
phi = 2.0 * np.pi * np.log(numbers)
order = 16
panel_width = 0.25
prefactor = (panel_width ** (2 * order + 1)
             * math.factorial(order) ** 4
             / ((2 * order + 1) * math.factorial(2 * order) ** 3))
weighted_phi_derivative_sum = float(np.sum(
    2.0 * lam / np.sqrt(numbers) * phi ** (2 * order)
))
cos_only_bound = prefactor * weight_max * weighted_phi_derivative_sum
result = {
    "record": 2327,
    "order": order,
    "panel_width": panel_width,
    "prime_count": int(numbers.size),
    "owner_weight_max_sampled": weight_max,
    "gauss_legendre_remainder_prefactor": prefactor,
    "weighted_phi_32_sum": weighted_phi_derivative_sum,
    "cos_only_remainder_bound": cos_only_bound,
    "cos_only_bound_over_margin": cos_only_bound / 1.675396046388e12,
    "status": "PARTIAL_REMAINDER_NOT_CERTIFICATE",
    "omitted_terms": ["derivatives of owner weight W", "endpoint correction", "finite-window/full-line tail"],
}
out = ROOT / "results" / "2327_cosine_remainder_headroom.json"
out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
print(json.dumps(result, indent=2, sort_keys=True))