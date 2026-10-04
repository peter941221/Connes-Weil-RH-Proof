"""Generate the base-pair sigma=+1/2 fine chain at production cell 2700.

Record 2571 stage A. The 2558 signed-cell generator is sign-parameterized,
but the committed 2558 chain covers only sigma = -1/2 at cells 2700/2701:
the sigma = +1/2 cell2700 certificate of record 2563 still rests on the
coarse 2551 boundary envelope, whose statement is instantiated at the base
pair only. This driver renders Cell(2700, +1) through the committed
generator, emitting the seven-module fine chain (Midpoint, Left/Right
norm bounds, MidpointBounds, Fourth, Assembly, Integral) at the base pair,
so the plus sign carries the same aggregate layer the minus sign received
in 2558. Stage B regenerates the correction-pair modules from these exactly
as 2570 regenerated the minus chain.

The per-family leaves are coefficient-independent; every aggregate theorem
is instantiated at the record-2338 ideal_base_coefficient rows. Endpoint
and value modules (kernel N02700/N02701 Plus of 2555, shared Plus of 2556)
are already committed and are only read.
"""
import json

from generate_signed_cells_2558 import ROOT, Cell, write

RECORD = 2571
CELL = Cell(2700, 1)

PARTS = ("Midpoint", "LeftBounds", "RightBounds", "MidpointBounds",
         "Fourth", "Assembly", "Integral")


def main():
    write(CELL.module("Midpoint"), CELL.render_midpoint())
    for side in ("Left", "Right"):
        write(CELL.module(side + "Bounds"), CELL.render_norm(side))
    bounds_source, upper, charge = CELL.render_midpoint_bounds()
    write(CELL.module("MidpointBounds"), bounds_source)
    write(CELL.module("Fourth"), CELL.render_fourth())
    write(CELL.module("Assembly"), CELL.render_assembly())
    integral_source, info = CELL.render_integral()
    write(CELL.module("Integral"), integral_source)
    result = dict(
        record=RECORD, cell=CELL.index, sign=CELL.sign,
        midpoint_upper=str(upper), midpoint_charge=str(charge),
        integral=info,
        modules=[CELL.module(part) for part in PARTS])
    path = ROOT / f"results/{RECORD}_plus_cell2700_base_inputs.json"
    path.write_text(json.dumps(result, indent=2) + "\n")
    print("PLUS_CELL2700_BASE_CHAIN_GENERATED",
          json.dumps({k: v for k, v in result.items() if k != "modules"}),
          flush=True)


if __name__ == "__main__":
    main()
