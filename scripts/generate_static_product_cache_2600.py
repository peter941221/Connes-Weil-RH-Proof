"""Generate a sharded exact-product cache for record 2600."""

import argparse
import json
from pathlib import Path

from generate_static_defect_bounds_2600 import (
    DEV,
    WITNESS,
    fin_literal,
    interval_rect,
    point_rect,
    product_rect,
)


def product_theorem(row: int, column: int, inner: int, matrix: list[list[dict]], inverse: list[list[dict]]) -> str:
    name = f"candidateInverseAnalyticProduct2600_{row:02d}_{column:02d}_{inner:02d}"
    row_index = fin_literal(row)
    column_index = fin_literal(column)
    inner_index = fin_literal(inner)
    left_point = point_rect(inverse[row][inner]).replace(chr(10), " ")
    right_interval = interval_rect(matrix[inner][column]).replace(chr(10), " ")
    product = product_rect(inverse[row][inner], matrix[inner][column])
    return f'''theorem {name} :
    (candidateInverseInterval2600 {row_index} {inner_index}).mul
      (analyticMomentInterval2597 {inner_index} {column_index}) =
    {product} := by
  change ComplexRect2427.mul ({left_point} : ComplexRect2427)
      ({right_interval} : ComplexRect2427) =
    {product}
  norm_num [ComplexRect2427.mul,
    RealInterval2429.add, RealInterval2429.mul, RealInterval2429.sub,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ]
'''


def row_module(row: int, matrix: list[list[dict]], inverse: list[list[dict]]) -> str:
    theorems = [
        product_theorem(row, column, inner, matrix, inverse)
        for column in range(30)
        for inner in range(30)
    ]
    return f'''import ConnesWeilRH.Dev.C1RouteACorrectionStaticDefectBounds2600Common

/-! Exact product cache for record 2600, candidate-inverse row {row:02d}. -/

namespace ConnesWeilRH.Dev

{chr(10).join(theorems)}

end ConnesWeilRH.Dev
'''


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("row", type=int)
    args = parser.parse_args()
    if not 0 <= args.row < 30:
        raise ValueError("row must be in [0, 29]")
    payload = json.loads(WITNESS.read_text(encoding="utf-8"))
    output = DEV / f"C1RouteACorrectionStaticDefectProductCache2600Row{args.row:02d}.lean"
    output.write_text(row_module(args.row, payload["matrix"], payload["candidate_inverse"]), encoding="utf-8")
    print(output)


if __name__ == "__main__":
    main()
