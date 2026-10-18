"""Build rational order-20 sin/cos endpoint enclosures for subcell 0."""
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path


PI_LO = Q(314159265358979323846264338327950288419716939937510, 10**50)
PI_HI = Q(314159265358979323846264338327950288419716939937511, 10**50)
CELLS = 256
PARENT = 214
SUBDIVISIONS = 8
ORDER = 20


def taylor_sin(x):
    return sum(((-1) ** j) * x ** (2 * j + 1) / Q(_fact(2 * j + 1))
               for j in range(ORDER + 1))


def taylor_cos(x):
    return sum(((-1) ** j) * x ** (2 * j) / Q(_fact(2 * j))
               for j in range(ORDER + 1))


def _fact(n):
    out = 1
    for k in range(2, n + 1):
        out *= k
    return out


def endpoint(label, pi_value):
    cell_width = Q(2) * pi_value / CELLS
    lo = Q(2) * pi_value * PARENT / CELLS
    hi = lo + cell_width / SUBDIVISIONS
    x = lo if label == "left" else hi
    sin_poly, cos_poly = taylor_sin(x), taylor_cos(x)
    # Taylor remainder is bounded by |x|^(N+1)/(N+1)!; pi-bracket
    # propagation is bounded by the pi bracket width via the 1-Lipschitz laws.
    rem_s = abs(x) ** (ORDER + 1) / Q(_fact(ORDER + 1))
    rem_c = abs(x) ** (ORDER + 1) / Q(_fact(ORDER + 1))
    return {
        "endpoint": label,
        "x_lo": str(x),
        "sin_lo": str(sin_poly - rem_s),
        "sin_hi": str(sin_poly + rem_s),
        "cos_lo": str(cos_poly - rem_c),
        "cos_hi": str(cos_poly + rem_c),
        "pi_width": str(PI_HI - PI_LO),
    }


def main():
    rows = [endpoint(label, pi_value)
            for label in ("left", "right")
            for pi_value in (PI_LO, PI_HI)]
    payload = {
        "record": 2914,
        "order": ORDER,
        "rows": rows,
        "generator_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "claims": {"rational_taylor_replay": True,
                    "formal_taylor_certificate": False},
        "nonclaims": ["No Lean pi-bound theorem is connected yet"],
    }
    out = Path("results/2914_route_b_trig_taylor_rational.json")
    out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(payload, indent=2))


if __name__ == "__main__":
    main()
