"""Generate small exact coordinate-sum blocks for the Row00 cache probe."""

import argparse
import json
from fractions import Fraction
from pathlib import Path

from generate_static_defect_bounds_2600 import (
    DEV,
    WITNESS,
    fin_literal,
    interval_add,
    interval_neg,
    interval_product,
    real_expr,
)


def product_coords(left: dict, right: dict) -> dict[str, Fraction]:
    left_real = (Fraction(left["real"]["lower_exact"]), Fraction(left["real"]["upper_exact"]))
    left_imag = (Fraction(left["imag"]["lower_exact"]), Fraction(left["imag"]["upper_exact"]))
    right_real = (Fraction(right["real"]["lower_exact"]), Fraction(right["real"]["upper_exact"]))
    right_imag = (Fraction(right["imag"]["lower_exact"]), Fraction(right["imag"]["upper_exact"]))
    real = interval_add(interval_product(left_real, right_real),
                        interval_neg(interval_product(left_imag, right_imag)))
    imag = interval_add(interval_product(left_real, right_imag),
                        interval_product(left_imag, right_real))
    return {"reLo": real[0], "reHi": real[1], "imLo": imag[0], "imHi": imag[1]}


def block_theorem(column: int, block: int, coordinate: str, matrix: list[list[dict]], inverse: list[list[dict]]) -> str:
    start = block * 5
    indices = list(range(start, start + 5))
    terms = [
        f"((candidateInverseInterval2600 0 {fin_literal(inner)}).mul\n"
        f"        (analyticMomentInterval2597 {fin_literal(inner)} {fin_literal(column)})).{coordinate}"
        for inner in indices
    ]
    total = sum(
        (product_coords(inverse[0][inner], matrix[inner][column])[coordinate] for inner in indices),
        Fraction(0),
    )
    theorem = f"candidateInverseAnalyticSumBlock2600_00_{column:02d}_{block}_{coordinate}"
    names = [f"candidateInverseAnalyticProduct2600_00_{column:02d}_{inner:02d}" for inner in indices]
    return f'''theorem {theorem} :
    {' + '.join(terms)} = {real_expr(str(total))} := by
  rw [{', '.join(names)}]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]
'''


def module_source(column: int, payload: dict) -> str:
    if not 0 <= column < 30:
        raise ValueError("column must be in [0, 29]")
    matrix = payload["matrix"]
    inverse = payload["candidate_inverse"]
    indices = [fin_literal(index) for index in range(30)]
    block_sums = []
    for block in range(6):
        terms = indices[block * 5:(block + 1) * 5]
        block_sums.append("(" + " + ".join(f"f {index}" for index in terms) + ")")
    decomposition = " + ".join(block_sums)
    generic = f'''theorem fin30_sum_eq_six_blocks (f : Fin 30 → ℝ) :
    (∑ k : Fin 30, f k) = {decomposition} := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  ring

'''
    theorems = [
        block_theorem(column, block, coordinate, matrix, inverse)
        for block in range(6)
        for coordinate in ("reLo", "reHi", "imLo", "imHi")
    ]
    dependency = ("C1RouteACorrectionStaticDefectProductCache2600Row00" if column == 0
                  else "C1RouteACorrectionStaticDefectSumBlocks2600Row00Col00")
    return (
        f"import ConnesWeilRH.Dev.{dependency}\n\n"
        "namespace ConnesWeilRH.Dev\n\n"
        + (generic if column == 0 else "")
        + "\n".join(theorems)
        + "\nend ConnesWeilRH.Dev\n"
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--column", type=int, default=0)
    args = parser.parse_args()
    payload = json.loads(WITNESS.read_text(encoding="utf-8"))
    source = module_source(args.column, payload)
    output = DEV / f"C1RouteACorrectionStaticDefectSumBlocks2600Row00Col{args.column:02d}.lean"
    output.write_text(source, encoding="utf-8")
    print(output)


if __name__ == "__main__":
    main()
