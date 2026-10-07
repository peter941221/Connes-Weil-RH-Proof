"""Generate separately checked coordinate sums and a direct 2600 cell bound."""

import argparse
import json
from fractions import Fraction

from generate_static_defect_bounds_2600 import DEV, WITNESS, fin_literal, real_expr
from generate_static_sum_blocks_2600 import module_source, product_coords
from generate_static_product_cache_2600 import row_module as product_cache_source


COORDINATES = ("reLo", "reHi", "imLo", "imHi")
SUFFIXES = {"reLo": "ReLo", "reHi": "ReHi", "imLo": "ImLo", "imHi": "ImHi"}
SUM_PREFIX = "C1RouteACorrectionStaticDefectSum2617Cell"
CONVERTED_ROWS = frozenset(range(30))


def validate_payload(payload: dict) -> None:
    if payload.get("record") != 2351 or payload.get("dimension") != 30:
        raise ValueError("expected the record-2351 dimension-30 witness")
    for key in ("matrix", "candidate_inverse"):
        rows = payload[key]
        if len(rows) != 30 or any(len(row) != 30 for row in rows):
            raise ValueError(f"expected a 30 by 30 {key}")
        for row in rows:
            for entry in row:
                for component in ("real", "imag"):
                    lower = Fraction(entry[component]["lower_exact"])
                    upper = Fraction(entry[component]["upper_exact"])
                    if lower > upper:
                        raise ValueError("inverted witness interval")
                    if key == "candidate_inverse" and lower != upper:
                        raise ValueError("candidate inverse must use point rectangles")


def compute_coordinates(payload: dict, column: int = 0,
                        row: int = 0) -> tuple[dict, dict, Fraction, Fraction]:
    if not 0 <= column < 30:
        raise ValueError("column must be in [0, 29]")
    if not 0 <= row < 30:
        raise ValueError("row must be in [0, 29]")
    matrix = payload["matrix"]
    inverse = payload["candidate_inverse"]
    sums = {
        coordinate: sum(
            (product_coords(inverse[row][inner], matrix[inner][column])[coordinate]
             for inner in range(30)),
            Fraction(0),
        )
        for coordinate in COORDINATES
    }
    defect = {
        "reLo": Fraction(int(column == row)) - sums["reHi"],
        "reHi": Fraction(int(column == row)) - sums["reLo"],
        "imLo": -sums["imHi"],
        "imHi": -sums["imLo"],
    }
    real_bound = max(abs(defect["reLo"]), abs(defect["reHi"]))
    imag_bound = max(abs(defect["imLo"]), abs(defect["imHi"]))
    return sums, defect, real_bound, imag_bound


def sum_source(coordinate: str, value: Fraction, column: int = 0,
               row: int = 0) -> str:
    column_index = fin_literal(column)
    row_index = fin_literal(row)
    blocks = ", ".join(
        f"candidateInverseAnalyticSumBlock2600_{row:02d}_{column:02d}_{block}_{coordinate}"
        for block in range(6)
    )
    return f'''import ConnesWeilRH.Dev.C1RouteACorrectionStaticDefectSumBlocks2600Row{row:02d}Col{column:02d}

namespace ConnesWeilRH.Dev

theorem candidateInverseAnalyticSum2617_{row:02d}_{column:02d}_{coordinate} :
    (∑ k : Fin 30, ((candidateInverseInterval2600 {row_index} k).mul
      (analyticMomentInterval2597 k {column_index})).{coordinate}) =
    {real_expr(str(value))} := by
  rw [fin30_sum_eq_six_blocks]
  rw [{blocks}]
  norm_num

end ConnesWeilRH.Dev
'''


def bound_source(real_bound: Fraction, imag_bound: Fraction, column: int = 0,
                 row: int = 0) -> str:
    column_index = fin_literal(column)
    row_index = fin_literal(row)
    diagonal_guard = (f"  have hdiag : ({row_index} : Fin 30) ≠ {column_index} := by decide\n"
                      if column != row else "")
    diagonal_rewrite = "    rw [if_neg hdiag]\n" if column != row else ""
    imports = "\n".join(
        f"import ConnesWeilRH.Dev.{SUM_PREFIX}{row:02d}{column:02d}{SUFFIXES[coordinate]}"
        for coordinate in COORDINATES
    )
    source_coordinates = {
        "reLo": "reHi", "reHi": "reLo", "imLo": "imHi", "imHi": "imLo"
    }
    steps = "\n".join(
        f'''  · rw [matrixDefectInterval2598_{coordinate},
      candidateInverseAnalyticSum2617_{row:02d}_{column:02d}_{source_coordinates[coordinate]}]
{diagonal_rewrite}    norm_num'''
        for coordinate in COORDINATES
    )
    return f'''import ConnesWeilRH.Dev.C1RouteACorrectionCoordinateBound2617
{imports}

namespace ConnesWeilRH.Dev

theorem candidateInverseDefectEntryBound2617_{row:02d}_{column:02d} :
    rectL1Upper2598 (matrixDefectInterval2598
      candidateInverseInterval2600 analyticMomentInterval2597 {row_index} {column_index}) ≤
      analyticDefectEntryBounds2595 {row_index} {column_index} := by
{diagonal_guard}  apply rectL1Upper2598_le_of_coordinate_bounds2617
    (realBound := {real_expr(str(real_bound))})
    (imagBound := {real_expr(str(imag_bound))})
{steps}
  · change {real_expr(str(real_bound))} + {real_expr(str(imag_bound))} ≤
      {real_expr(str(real_bound + imag_bound))}
    norm_num

end ConnesWeilRH.Dev
'''


def generated_sources(payload: dict, column: int = 0, row: int = 0) -> dict[str, str]:
    validate_payload(payload)
    sums, _, real_bound, imag_bound = compute_coordinates(payload, column, row)
    sources = {
        f"{SUM_PREFIX}{row:02d}{column:02d}{SUFFIXES[coordinate]}.lean":
        sum_source(coordinate, sums[coordinate], column, row)
        for coordinate in COORDINATES
    }
    sources[f"C1RouteACorrectionStaticDefectCoordinate2617Cell{row:02d}{column:02d}.lean"] = bound_source(
        real_bound, imag_bound, column, row)
    sources[f"C1RouteACorrectionStaticDefectCoordinate2617Cell{row:02d}{column:02d}Audit.lean"] = f'''import ConnesWeilRH.Dev.C1RouteACorrectionStaticDefectCoordinate2617Cell{row:02d}{column:02d}

#print axioms ConnesWeilRH.Dev.candidateInverseDefectEntryBound2617_{row:02d}_{column:02d}
'''
    if column != 0:
        sources[f"C1RouteACorrectionStaticDefectSumBlocks2600Row{row:02d}Col{column:02d}.lean"] = module_source(
            column, payload, row)
    return sources


def row_facade_source(row: int = 0) -> str:
    row_index = fin_literal(row)
    imports = "\n".join(
        f"import ConnesWeilRH.Dev.C1RouteACorrectionStaticDefectCoordinate2617Cell{row:02d}{column:02d}"
        for column in range(30)
    )
    cells = "\n".join(
        f'''theorem candidateInverseDefectEntryBound2600_cell_{row:02d}_{column:02d} :
    rectL1Upper2598 (matrixDefectInterval2598
      candidateInverseInterval2600 analyticMomentInterval2597 {row_index} {fin_literal(column)}) ≤
      analyticDefectEntryBounds2595 {row_index} {fin_literal(column)} :=
  candidateInverseDefectEntryBound2617_{row:02d}_{column:02d}
'''
        for column in range(30)
    )
    dispatch = "\n".join(
        f"  · exact candidateInverseDefectEntryBound2600_cell_{row:02d}_{column:02d}"
        for column in range(30)
    )
    return f'''{imports}

namespace ConnesWeilRH.Dev

{cells}
theorem candidateInverseDefectEntryBound2600_row_{row:02d} (j : Fin 30) :
    rectL1Upper2598 (matrixDefectInterval2598
      candidateInverseInterval2600 analyticMomentInterval2597 {row_index} j) ≤
      analyticDefectEntryBounds2595 {row_index} j := by
  fin_cases j
{dispatch}

end ConnesWeilRH.Dev
'''


def generated_row_sources(payload: dict, row: int = 0) -> dict[str, str]:
    sources = {}
    for column in range(30):
        sources.update(generated_sources(payload, column, row))
    sources[f"C1RouteACorrectionStaticDefectSumBlocks2600Row{row:02d}Col00.lean"] = module_source(
        0, payload, row)
    sources[f"C1RouteACorrectionStaticDefectProductCache2600Row{row:02d}.lean"] = product_cache_source(
        row, payload["matrix"], payload["candidate_inverse"])
    sources[f"C1RouteACorrectionStaticDefectBounds2600Row{row:02d}.lean"] = row_facade_source(row)
    sources[f"C1RouteACorrectionStaticDefectCoordinate2617Row{row:02d}Audit.lean"] = f'''import ConnesWeilRH.Dev.C1RouteACorrectionStaticDefectBounds2600Row{row:02d}

#print axioms ConnesWeilRH.Dev.candidateInverseDefectEntryBound2600_row_{row:02d}
'''
    return sources


def main() -> None:
    parser = argparse.ArgumentParser()
    options = parser.add_mutually_exclusive_group()
    options.add_argument("--column", type=int, default=0)
    options.add_argument("--all-columns", action="store_true")
    args = parser.parse_args()
    payload = json.loads(WITNESS.read_text(encoding="utf-8"))
    sources = (generated_row_sources(payload) if args.all_columns
               else generated_sources(payload, args.column))
    for filename, source in sources.items():
        output = DEV / filename
        output.write_text(source, encoding="utf-8")
        print(output.relative_to(DEV.parent.parent))


if __name__ == "__main__":
    main()
