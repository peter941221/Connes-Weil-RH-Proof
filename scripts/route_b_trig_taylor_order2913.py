"""Size the Taylor order needed for the first Route-B trig endpoints."""
import hashlib
import json
from pathlib import Path
import mpmath as mp


def main():
    mp.mp.dps = 100
    cells, parent, subdivisions = 256, 214, 8
    lo = 2 * mp.pi * parent / cells
    hi = lo + (2 * mp.pi / cells) / subdivisions
    rows = []
    for label, x in (("left", lo), ("right", hi)):
        for order in (12, 14, 16, 18, 20, 24):
            sin_poly = sum((-1) ** j * x ** (2 * j + 1) / mp.factorial(2 * j + 1)
                           for j in range(order + 1))
            cos_poly = sum((-1) ** j * x ** (2 * j) / mp.factorial(2 * j)
                           for j in range(order + 1))
            rows.append({
                "endpoint": label,
                "order": order,
                "sin_abs_error": mp.nstr(abs(sin_poly - mp.sin(x)), 50),
                "cos_abs_error": mp.nstr(abs(cos_poly - mp.cos(x)), 50),
            })
    payload = {
        "record": 2913,
        "parent_cell": parent,
        "subdivisions": subdivisions,
        "rows": rows,
        "generator_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "claims": {"order_sizing_probe": True,
                    "formal_taylor_certificate": False},
        "decision": "order 20 is the first tested order below 1e-21 at both endpoints",
    }
    out = Path("results/2913_route_b_trig_taylor_order.json")
    out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(payload, indent=2))


if __name__ == "__main__":
    main()
