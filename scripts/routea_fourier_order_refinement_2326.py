"""Record 2326: same-panel GL16 versus GL32 Fourier probe."""
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
carrier = e2308.evaluator.bridge.refined.remainder.carrier
source = carrier.SOURCE
primes = source.rig.prime_powers_up_to(
    math.exp(2.0 * max(width * width for width, _ in families))
)
numbers = np.asarray([number for number, _ in primes], dtype=np.int64)
lam = np.asarray([weight for _, weight in primes], dtype=float)
mask = numbers > 167
numbers, lam = numbers[mask], lam[mask]

values16, signed16, abs16 = probe.coefficients(
    16, 320, numbers, lam, rho, families, xw, base, correction
)
values32, signed32, abs32 = probe.coefficients(
    32, 320, numbers, lam, rho, families, xw, base, correction
)
result = {
    "record": 2326,
    "panel_count": 320,
    "panel_width": 0.25,
    "prime_count": int(numbers.size),
    "gl16_signed": signed16,
    "gl32_signed": signed32,
    "gl16_abs_sum": abs16,
    "gl32_abs_sum": abs32,
    "gl32_minus_gl16_signed": float(np.sum(values32 - values16)),
    "gl32_minus_gl16_abs_sum": float(np.sum(np.abs(values32 - values16))),
    "status": "SAME_PANEL_ORDER_DIAGNOSTIC_NOT_CERTIFICATE",
}
out = ROOT / "results" / "2326_fourier_order_refinement.json"
out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
print(json.dumps(result, indent=2, sort_keys=True))