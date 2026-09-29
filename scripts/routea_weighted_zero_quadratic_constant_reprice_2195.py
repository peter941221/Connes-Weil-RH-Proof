"""Reprice the 2195 sampled lower screen with an explicit xi(2) proxy.

This does not alter the sampled transform result. It only supplies the
normalization scale used by completedRiemannXi at s=2 for this diagnostic
calculation. It remains non-certified and candidate-only.
"""
import json
import math
import os
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
src = ROOT / "results" / "2195_weighted_zero_quadratic_constant_screen.json"
dst = ROOT / "results" / "2195_weighted_zero_quadratic_constant_reprice.json"
data = json.loads(src.read_text(encoding="utf-8"))
xi2_proxy = math.pi / 6.0
kernel_small = (1.0 / math.pi) ** 0.25 * math.gamma(0.25)
xi_tail = 2.0 / (1.0 - math.exp(-math.pi))
xi_growth = 2.0 * xi_tail * (kernel_small + 1.0)
mult = (xi_growth + 1.0 + abs(math.log(xi2_proxy)) + 192.0) / math.log(2.0)
b = data["screen"]["B_lower"]
tail = 4.0 * mult * b
data["record"] = 2195
data["status"] = "CANDIDATE-LOWER-SCREEN-REPRICED"
data["screen"]["xi2_proxy"] = xi2_proxy
data["screen"]["spectralMultiplicityConstant_proxy"] = mult
data["screen"]["high_shell_budget_lower"] = tail
data["screen"]["tail_lower_over_margin"] = tail / data["screen"]["signed_margin_anchor"]
data["provenance"]["reprice_script"] = os.fspath(Path(__file__).relative_to(ROOT))
dst.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
print(json.dumps(data["screen"], indent=2))
