"""Price the actual 2562 decomposed strip upper on the correction grid.

External Arb enclosures of the 2539 analytic quantities at the 2570
correction centers and uniform 1e-28 error. This is not a Lean table
certificate, a membership proof or a generated-table rounding price.
"""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import time

from flint import acb, arb, ctx
import price_correction_second_2561 as direct
import routea_owner_whole_cell_2535 as base

ROOT = Path(__file__).resolve().parents[1]
PIN = direct.PIN
ERROR = Fraction(1, 10 ** 28)
PRODUCTION_CELLS = 10240


def load_families():
    families = base.load_families()
    rows = json.loads(base.REPAIR.read_text())["coefficient_rows"]
    for family, row in zip(families, rows):
        box = row["ideal_correction_coefficient"]
        bounds = [tuple(Fraction(box[part][side]) for side in
                        ("lower_exact", "upper_exact")) for part in ("real", "imag")]
        assert all(lower <= upper for lower, upper in bounds)
        centers = [(lower + upper) / 2 for lower, upper in bounds]
        assert sum((upper - lower) / 2 for lower, upper in bounds) <= ERROR
        family["center"] = acb(*(base.lift(value) for value in centers))
        family["error"] = base.lift(ERROR)
        family["scale"] = base.upper(sum((base.lift(abs(value)) for value in centers),
                                         arb(0)) + family["error"])
    return families


def point_data(families, position, sigma, order):
    weight = base.lift(sigma)
    center = acb(0)
    error = arb(0)
    thirds = []
    for family in families:
        jets = base.atom_jets(family, position, weight, order)
        center += family["center"] * jets[0]
        error += family["error"] * abs(jets[0])
        if order >= 3:
            thirds.append(base.upper(abs(jets[3])))
    return base.upper(abs(center) + error), thirds


def cell_data(families, cells, index, sigma, left_data=None, right_data=None):
    step = 2 * base.RADIUS / cells
    width = base.lift(step)
    weight = base.lift(sigma)
    left = -base.RADIUS + index * step
    right = left + step
    midpoint = (left + right) / 2
    if left_data is None:
        left_data = point_data(families, left, sigma, 3)
    if right_data is None:
        right_data = point_data(families, right, sigma, 3)
    centers = [acb(0), acb(0)]
    errors = [arb(0), arb(0)]
    third = arb(0)
    fourth = arb(0)
    for family, left_third, right_third in zip(families, left_data[1], right_data[1]):
        jets = base.atom_jets(family, midpoint, weight, 2)
        for offset, order in enumerate((1, 2)):
            centers[offset] += family["center"] * jets[order]
            errors[offset] += family["error"] * abs(jets[order])
        envelope = base.fourth_envelope(family, left, right, weight)
        third += family["scale"] * (max(left_third, right_third) + width / 2 * envelope)
        fourth += family["scale"] * envelope
    first = base.exact_upper(abs(centers[0]) + errors[0])
    second = base.exact_upper(abs(centers[1]) + errors[1])
    third_bound = base.exact_upper(third)
    curvature = second + step / 2 * third_bound
    left_upper = base.exact_upper(left_data[0])
    right_upper = base.exact_upper(right_data[0])
    curvature_piece = step * curvature
    first_piece = 2 * abs(sigma) * step * (first + curvature * step / 2)
    value_piece = sigma ** 2 * (step / 2 * (left_upper + right_upper) +
                              curvature * step ** 3 / 12)
    total = curvature_piece + first_piece + value_piece
    affine = ((step + abs(sigma) * step ** 2 + sigma ** 2 * step ** 3 / 12) * curvature +
              2 * abs(sigma) * step * first + sigma ** 2 * step / 2 *
              (left_upper + right_upper))
    assert total == affine
    return dict(index=index, curvature=curvature, first=first,
                endpoints=left_upper + right_upper, second=second,
                third=third_bound, fourth=base.exact_upper(fourth),
                curvature_piece=curvature_piece, first_piece=first_piece,
                value_piece=value_piece, total=total)


def anchor_controls(families):
    readings = []
    for record, index, sign in ((2570, 2700, -1), (2571, 2700, 1), (2572, 2701, -1)):
        reference = json.loads((ROOT / f"results/{record}_generation_readback.json").read_text())
        row = cell_data(families, PRODUCTION_CELLS, index, Fraction(sign, 2))
        bound = Fraction(reference["cell_bound"])
        assert row["total"] <= bound, (record, float(row["total"]), float(bound))
        assert row["total"] * Fraction(101, 100) >= bound
        readings.append(dict(record=record, index=index, sign=sign,
                             total=str(row["total"]), committed_bound=str(bound),
                             committed_ratio=float(bound / row["total"])))
    return readings


def run_grid(families, cells, sign):
    sigma = Fraction(sign, 2)
    step = 2 * base.RADIUS / cells
    sums = {key: Fraction(0) for key in ("curvature", "first", "endpoints", "second",
                                       "third", "fourth", "curvature_piece",
                                       "first_piece", "value_piece", "total")}
    bins = [Fraction(0) for _ in range(16)]
    left_data = point_data(families, -base.RADIUS, sigma, 3)
    for index in range(cells):
        right_data = point_data(families, -base.RADIUS + (index + 1) * step, sigma, 3)
        row = cell_data(families, cells, index, sigma, left_data, right_data)
        for key in sums:
            sums[key] += row[key]
        bins[min(15, 16 * index // cells)] += row["total"]
        left_data = right_data
        if (index + 1) % 1024 == 0:
            print("DECOMPOSED", cells, sign, index + 1, flush=True)
    assert sum(bins) == sums["total"]
    affine = ((step + abs(sigma) * step ** 2 + sigma ** 2 * step ** 3 / 12) *
              sums["curvature"] + 2 * abs(sigma) * step * sums["first"] +
              sigma ** 2 * step / 2 * sums["endpoints"])
    assert affine == sums["total"]
    return dict(cells=cells, sign=sign, exact={key: str(value) for key, value in sums.items()},
                display={key: float(value) for key, value in sums.items()},
                profile=[str(value) for value in bins], fits_pin=sums["total"] <= PIN,
                margin=str(PIN - sums["total"]))


def reproduce_direct(cells):
    reference = json.loads((ROOT / f"results/2561_correction_second_{cells}.json").read_text())
    rows = [direct.run(cells, sign) for sign in (-1, 1)]
    for observed, committed in zip(rows, reference["rows"]):
        assert observed["sign"] == committed["sign"]
        for key in ("node", "remainder", "total", "margin", "fits_pin"):
            assert observed[key] == committed[key], (key, observed[key], committed[key])
    return dict(status="SAME_RUN_DIRECT_2561_EXACT_REPRODUCTION", rows=rows)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--cells", type=int, default=PRODUCTION_CELLS)
    parser.add_argument("--precision", type=int, default=192)
    parser.add_argument("--reproduce-direct", action="store_true")
    args = parser.parse_args()
    assert args.cells > 0 and args.precision >= 128
    ctx.prec = args.precision
    started = time.monotonic()
    families = load_families()
    controls = anchor_controls(families)
    direct_control = reproduce_direct(args.cells) if args.reproduce_direct else None
    rows = [run_grid(families, args.cells, sign) for sign in (-1, 1)]
    paths = [Path(__file__), Path(base.__file__), Path(direct.__file__), base.REPAIR,
             base.CAPTURE] + [ROOT / f"results/{record}_generation_readback.json"
                              for record in (2570, 2571, 2572)]
    if args.reproduce_direct:
        paths.append(ROOT / f"results/2561_correction_second_{args.cells}.json")
    result = dict(record=2573, status="EXTERNAL_DECOMPOSED_GRID_PRICE",
                  coefficient_row="ideal_correction_coefficient", error=str(ERROR),
                  curvature_weight="abs(real(center))+abs(imag(center))+error",
                  precision=args.precision, pin=str(PIN), rows=rows,
                  anchor_controls=controls, direct_control=direct_control,
                  analytic_grid_fits=all(row["fits_pin"] for row in rows),
                  production_grid=args.cells == PRODUCTION_CELLS,
                  lean_certificate=False, table_rounding_priced=False,
                  exact_coefficient_membership=False, producer_go=False, rh_claim=False,
                  elapsed_seconds=time.monotonic() - started,
                  source_sha256={str(path.relative_to(ROOT)):
                                 hashlib.sha256(path.read_bytes()).hexdigest() for path in paths})
    out = ROOT / f"results/2573_decomposed_grid_{args.cells}.json"
    out.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps([row["display"] for row in rows]), flush=True)


if __name__ == "__main__":
    main()
