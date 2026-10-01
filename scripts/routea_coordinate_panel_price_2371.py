"""Price the coordinate and panel terms in the existing 2348 theorem shape.

This is a planning/price artifact: stored coefficient operands are evaluated
with mpmath, while the theorem-shaped obligations and the pointwise interval
certificate remain separate.  It must not be read as a producer certificate.
"""

import importlib.util
import json
import math
from pathlib import Path

import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]
mp.mp.dps = 80


def load_owner():
    spec = importlib.util.spec_from_file_location(
        "strip2371", ROOT / "scripts" / "routea_corrected_strip_envelope_2303.py"
    )
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def budget(order, families, coefficients):
    constants = [1, 60, 3720, 236160, 15130080]
    total = mp.mpf("0")
    for (radius, modulation), coefficient in zip(families, coefficients):
        radius = mp.mpf(radius)
        modulation = mp.mpf(modulation)
        coefficient_norm = mp.sqrt(mp.mpf(coefficient.real) ** 2 + mp.mpf(coefficient.imag) ** 2)
        family = mp.mpf("0")
        for index in range(order + 1):
            family += (
                math.comb(order, index)
                * abs(modulation) ** index
                * (constants[order - index] * mp.exp(-30) / radius ** (order - index))
            )
        total += coefficient_norm * family
    return total


def main():
    strip = load_owner()
    families, base, correction, _ = strip.load_owner()
    families = strip.corrected_fam(families)
    radius = mp.mpf(max(a for a, _ in families))
    outer_radius = mp.mpf("6.5536001")
    sigma = mp.mpf("-0.5")
    nodes = 240001
    step = 2 * radius / (nodes - 1)
    delta = mp.mpf(json.loads((ROOT / "results/2366_coordinate_pair_endpoint_certificate.json").read_text())[
        "coordinate_max_float_gap"
    ])
    rows = []
    for name, order, coefficients in (
        ("base_M0", 0, base), ("base_D2", 2, base),
        ("corr_M0", 0, correction), ("corr_D2", 2, correction),
    ):
        budgets = [budget(order + offset, families, coefficients) for offset in range(3)]
        coordinate_lipschitz = mp.exp(abs(sigma) * outer_radius) * (
            abs(sigma) * budgets[0] + budgets[1]
        )
        coordinate_charge = 2 * radius * coordinate_lipschitz * delta
        curvature = mp.exp(abs(sigma) * outer_radius) * (
            budgets[2] + 2 * abs(sigma) * budgets[1] + sigma ** 2 * budgets[0]
        )
        panel_remainder = step ** 2 * (2 * radius) * curvature / 12
        rows.append({
            "channel": name,
            "derivative_order": order,
            "budgets": [float(value) for value in budgets],
            "coordinate_lipschitz": float(coordinate_lipschitz),
            "coordinate_charge": float(coordinate_charge),
            "panel_remainder": float(panel_remainder),
            "coordinate_plus_panel": float(coordinate_charge + panel_remainder),
        })
    result = {
        "record": 2371,
        "status": "COORDINATE_AND_PANEL_REMAINDER_PRICE_NOT_CERTIFICATE",
        "nodes": nodes,
        "sigma": float(sigma),
        "radius": float(radius),
        "outer_radius": float(outer_radius),
        "coordinate_max_float_gap": float(delta),
        "rows": rows,
        "corr_D2_panel_to_directed_value": float(
            rows[3]["panel_remainder"] / 125446.71132157759
        ),
        "required_nodes_for_corr_D2_remainder_ratio": {
            str(ratio): int(math.ceil(
                1 + (nodes - 1) * math.sqrt(
                    rows[3]["panel_remainder"] / (ratio * 125446.71132157759)
                )
            )) for ratio in (0.5, 0.1, 0.01)
        },
        "theorem_shape": "step^2 * (2*radius) * weightedCurvature / 12",
        "stored_float_operands": True,
        "pointwise_interval_certificate": False,
        "directed_accumulation_certificate": False,
        "producer_go": False,
        "rh_claim": False,
    }
    (ROOT / "results/2371_coordinate_panel_price.json").write_text(
        json.dumps(result, indent=2) + "\n", encoding="utf-8"
    )
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
