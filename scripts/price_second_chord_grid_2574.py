"""Same-owner chord pricing for the weighted second-derivative integral.

Record 2574 changes only the second-integral method: endpoint W'' norms
plus h^3/12 times the existing whole-cell fourth-derivative upper. The
first/value channels and the correction pair stay unchanged. No Lean
numeric table certificate or exact-interpolant membership is asserted.
"""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import time

from flint import acb, arb, ctx
import price_decomposed_correction_grid_2573 as previous

ROOT = Path(__file__).resolve().parents[1]


def second_point(families, position, sigma):
    center = acb(0)
    error = arb(0)
    weight = previous.base.lift(sigma)
    for family in families:
        jet = previous.base.atom_jets(family, position, weight, 2)[2]
        center += family["center"] * jet
        error += family["error"] * abs(jet)
    return previous.base.exact_upper(abs(center) + error)


def run_chord(families, cells, sign, old_row):
    sigma = Fraction(sign, 2)
    step = 2 * previous.base.RADIUS / cells
    left = second_point(families, -previous.base.RADIUS, sigma)
    second_node = Fraction(0)
    for index in range(cells):
        right = second_point(families, -previous.base.RADIUS + (index + 1) * step, sigma)
        second_node += step / 2 * (left + right)
        left = right
        if (index + 1) % 2048 == 0:
            print("SECOND_CHORD", cells, sign, index + 1, flush=True)
    old_exact = {key: Fraction(value) for key, value in old_row["exact"].items()}
    fourth_remainder = step ** 3 / 12 * old_exact["fourth"]
    second_piece = second_node + fourth_remainder
    first_piece = old_exact["first_piece"]
    value_piece = old_exact["value_piece"]
    total = second_piece + first_piece + value_piece
    exact = dict(second_node=second_node, fourth_remainder=fourth_remainder,
                 second_piece=second_piece, first_piece=first_piece,
                 value_piece=value_piece, total=total)
    return dict(cells=cells, sign=sign, exact={key: str(value) for key, value in exact.items()},
                display={key: float(value) for key, value in exact.items()},
                margin=str(previous.PIN - total), fits_pin=total <= previous.PIN,
                old_total=str(old_exact["total"]), gain=float(old_exact["total"] / total))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--cells", type=int, default=previous.PRODUCTION_CELLS)
    args = parser.parse_args()
    assert args.cells > 0
    ctx.prec = 192
    started = time.monotonic()
    source = ROOT / f"results/2573_decomposed_grid_{args.cells}.json"
    committed = json.loads(source.read_text())
    families = previous.load_families()
    old_rows = [previous.run_grid(families, args.cells, sign) for sign in (-1, 1)]
    assert old_rows == committed["rows"], "same-run predecessor drift"
    rows = [run_chord(families, args.cells, sign, old_row)
            for sign, old_row in zip((-1, 1), old_rows)]
    paths = [Path(__file__), Path(previous.__file__), Path(previous.base.__file__),
             previous.base.REPAIR, previous.base.CAPTURE, source]
    result = dict(record=2574, status="EXTERNAL_SECOND_CHORD_GRID_PRICE", precision=192,
                  coefficient_row="ideal_correction_coefficient", error=str(previous.ERROR),
                  pin=str(previous.PIN), old_rows=old_rows, rows=rows,
                  predecessor_same_run="ALL_ROW_FIELDS_EXACTLY_REPRODUCED",
                  analytic_grid_fits=all(row["fits_pin"] for row in rows),
                  production_grid=args.cells == previous.PRODUCTION_CELLS,
                  lean_certificate=False, table_rounding_priced=False,
                  exact_coefficient_membership=False, producer_go=False, rh_claim=False,
                  elapsed_seconds=time.monotonic() - started,
                  source_sha256={str(path.relative_to(ROOT)):
                                 hashlib.sha256(path.read_bytes()).hexdigest() for path in paths})
    out = ROOT / f"results/2574_second_chord_grid_{args.cells}.json"
    out.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps([row["display"] for row in rows]), flush=True)


if __name__ == "__main__":
    main()
