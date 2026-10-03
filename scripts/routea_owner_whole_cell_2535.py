"""2535: signed-center Arb replay with analytic whole-cell fourth bounds.

External enclosure only. No Lean import or exact-owner transfer is asserted.
The fourth envelope couples exp(-30/q) with q**(-2*k), including support edges.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from math import comb
from pathlib import Path
import time

import flint
from flint import acb, arb, ctx

ROOT = Path(__file__).resolve().parents[1]
REPAIR = ROOT / "results/2338_exact_interpolation_repair.json"
CAPTURE = ROOT / "results/2275_gap_owner_audit.json"
RADIUS = Fraction(65536001, 10000000)
PIN = Fraction("2.7790943782")


def lift(value):
    value = Fraction(value)
    return arb(value.numerator) / value.denominator


def upper(value):
    if not value.is_finite():
        raise ValueError("nonfinite enclosure")
    return value.upper()


def exact_upper(value):
    bound = upper(value)
    # Flat support edges can have exp(-100000); never serialize their enormous
    # binary denominators or round them to zero. Book a positive 2^-128 floor.
    if 0 < bound < arb(2)**-128:
        return Fraction(1, 2**128)
    return Fraction(str(bound.fmpq()))


def numerators():
    """b^(k)(u) = exp(-30/q) P_k(u) / q^(2k), q=1-u^2."""
    result = [{0: 1}]
    for k in range(4):
        nxt = {}
        def add(p, c):
            nxt[p] = nxt.get(p, 0) + c
        for p, c in result[-1].items():
            add(p + 1, (4*k - 60)*c)
            add(p + 3, -4*k*c)
            if p:
                for shift, factor in ((-1, 1), (1, -2), (3, 1)):
                    add(p + shift, p*c*factor)
        result.append({p: c for p, c in nxt.items() if c})
    return result


POLYS = numerators()


def load_families():
    repair = json.loads(REPAIR.read_text())
    capture = json.loads(CAPTURE.read_text())["owner_capture"]
    if repair["capture_sha256"] != hashlib.sha256(CAPTURE.read_bytes()).hexdigest():
        raise ValueError("2338 capture provenance mismatch")
    rows, pairs = repair["coefficient_rows"], capture["families_hex"]
    if len(rows) != 30 or len(pairs) != 30:
        raise ValueError("expected 30 families")
    families = []
    for index, (row, pair) in enumerate(zip(rows, pairs)):
        if row["index"] != index:
            raise ValueError("coefficient row order mismatch")
        c = row["ideal_base_coefficient"]
        bounds = [tuple(Fraction(c[key][side]) for side in ("lower_exact", "upper_exact"))
                  for key in ("real", "imag")]
        if any(lo > hi for lo, hi in bounds):
            raise ValueError("reversed coefficient box")
        mids = [(lo + hi)/2 for lo, hi in bounds]
        half = [(hi - lo)/2 for lo, hi in bounds]
        center = acb(lift(mids[0]), lift(mids[1]))
        error = upper((lift(half[0])**2 + lift(half[1])**2).sqrt())
        r = Fraction.from_float(float.fromhex(pair[0]))**2
        theta = Fraction.from_float(float.fromhex(pair[1]))
        families.append(dict(r=r, radius=lift(r), theta=lift(theta),
                             theta_exact=theta, center=center, error=error,
                             scale=upper(abs(center) + error)))
    return families


def atom_jets(f, x_exact, sigma, order=3):
    if abs(x_exact) >= f["r"]:
        return [acb(0) for _ in range(order + 1)]
    x = lift(x_exact)
    u = x / f["radius"]
    q = 1-u*u
    if not q > 0:
        raise ValueError("unresolved interior deficit")
    exponential = acb(-30/q + sigma*x, f["theta"]*x).exp()
    lam = acb(sigma, f["theta"])
    bump = [sum((c*u**p for p, c in POLYS[k].items()), arb(0))
            / (f["radius"]**k * q**(2*k)) for k in range(order + 1)]
    return [exponential * sum((comb(k, j)*lam**(k-j)*bump[j]
                              for j in range(k+1)), acb(0))
            for k in range(order+1)]


def fourth_envelope(f, a, b, sigma):
    """Bound all points, including a cell crossing a flat support junction.

    t=1/(1-u^2)>=1. exp(-30t)*t^(2k) decreases for k<=4.
    Polynomial magnitudes use max |u|; the coupled exponential uses min |u|.
    """
    near = Fraction(0) if a <= 0 <= b else min(abs(a), abs(b))
    if near >= f["r"]:
        return arb(0)
    far = min(max(abs(a), abs(b)), f["r"])
    u_min, u_max = lift(near/f["r"]), lift(far/f["r"])
    t = 1/(1-u_min*u_min)
    damp = (-30*t).exp()
    lam_abs = abs(acb(sigma, f["theta"]))
    weight = (sigma*lift(b if sigma > 0 else a)).exp()
    total = arb(0)
    for k in range(5):
        polynomial = sum((abs(c)*u_max**p for p, c in POLYS[k].items()), arb(0))
        total += comb(4, k)*lam_abs**(4-k)*polynomial*damp*t**(2*k)/f["radius"]**k
    return upper(weight*total)


def point_data(families, x, sigma):
    center, error = acb(0), arb(0)
    thirds = []
    for f in families:
        jets = atom_jets(f, x, sigma)
        center += f["center"]*jets[0]
        error += f["error"]*abs(jets[0])
        thirds.append(upper(abs(jets[3])))
    return upper(abs(center)+error), thirds


def run_grid(families, cells, sigma_exact, include_rows):
    sigma, h = lift(sigma_exact), lift(2*RADIUS/cells)
    step = 2*RADIUS/cells
    left_node, left_thirds = point_data(families, -RADIUS, sigma)
    node_total, curvature, fourth_charge = arb(0), arb(0), arb(0)
    node_payload_sum, remainder_payload_sum = Fraction(0), Fraction(0)
    rows = []
    for index in range(cells):
        a, b = -RADIUS+index*step, -RADIUS+(index+1)*step
        right_node, right_thirds = point_data(families, b, sigma)
        center2, error2, third, fourth = acb(0), arb(0), arb(0), arb(0)
        for j, f in enumerate(families):
            jet2 = atom_jets(f, (a+b)/2, sigma, 2)[2]
            center2 += f["center"]*jet2
            error2 += f["error"]*abs(jet2)
            third += f["scale"]*max(left_thirds[j], right_thirds[j])
            fourth += f["scale"]*fourth_envelope(f, a, b, sigma)
        # Each family third derivative: endpoint maximum + (h/2)*sup fourth.
        m2 = upper(abs(center2)+error2+h/2*(third+h/2*fourth))
        node = upper(h/2*(left_node+right_node))
        remainder = upper(h**3/12*m2)
        node_total += node
        curvature += remainder
        fourth_charge += h**5/48*fourth
        node_exact = exact_upper(node)
        remainder_exact = exact_upper(remainder)
        node_payload_sum += node_exact
        remainder_payload_sum += remainder_exact
        if include_rows:
            rows.append(dict(index=index, left_exact=str(a), right_exact=str(b),
                             node_upper_exact=str(node_exact),
                             second_upper_exact=str(exact_upper(m2)),
                             remainder_upper_exact=str(remainder_exact)))
        left_node, left_thirds = right_node, right_thirds
        if (index+1) % 1024 == 0:
            print("cells", cells, "sigma", sigma_exact, "completed", index+1, flush=True)
    node_bound = max(exact_upper(node_total), node_payload_sum)
    remainder_bound = max(exact_upper(curvature), remainder_payload_sum)
    total = node_bound + remainder_bound
    output = dict(cells=cells, sigma_exact=str(sigma_exact),
                  node_upper_exact=str(node_bound),
                  remainder_upper_exact=str(remainder_bound),
                  fourth_inflation_upper_exact=str(exact_upper(fourth_charge)),
                  total_upper_exact=str(total),
                  margin_lower_exact=str(PIN-total),
                  fits_pin=total < PIN)
    output["display"] = {key: float(Fraction(value)) for key, value in output.items()
                         if key.endswith("_exact") and key != "sigma_exact"}
    if include_rows:
        output["rows"] = rows
    return output


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--cells", type=int, default=10240)
    parser.add_argument("--bits", type=int, default=192)
    parser.add_argument("--rows", action="store_true")
    parser.add_argument("--output", type=Path, default=ROOT/"results/2535_whole_cell_enclosure.json")
    args = parser.parse_args()
    if args.cells <= 0 or args.bits < 128:
        raise ValueError("positive cell count and at least 128 bits required")
    ctx.prec = args.bits
    started = time.monotonic()
    families = load_families()
    endpoints = [run_grid(families, args.cells, sign, args.rows)
                 for sign in (Fraction(-1, 2), Fraction(1, 2))]
    result = dict(record=2535, status="EXTERNAL_WHOLE_CELL_ENCLOSURE_NOT_LEAN",
                  precision_bits=ctx.prec, python_flint_version=flint.__version__,
                  source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  input_sha256={str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
                                for path in (REPAIR, CAPTURE)},
                  radius_exact=str(RADIUS), pin_exact=str(PIN), endpoints=endpoints,
                  positive_export_floor_exact=str(Fraction(1, 2**128)),
                  all_fit=all(row["fits_pin"] for row in endpoints),
                  elapsed_seconds=time.monotonic()-started,
                  scope="base coefficient boxes only; analytic derivative/envelope argument external",
                  lean_certificate_imported=False, exact_owner_transfer=False,
                  complete_signed_kernel_priced=False, producer_go=False, rh_claim=False)
    args.output.write_text(json.dumps(result, indent=2)+"\n", encoding="utf-8")
    print(json.dumps({"all_fit": result["all_fit"],
                      "endpoints": [row["display"] for row in endpoints],
                      "elapsed_seconds": result["elapsed_seconds"]}), flush=True)


if __name__ == "__main__":
    main()
