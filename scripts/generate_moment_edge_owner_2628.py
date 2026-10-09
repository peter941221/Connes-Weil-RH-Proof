"""Generate the owner-d edge pair (record-2635 generalization of 2634's ad-hoc step).

Emits, for one diagonal owner d >= 1:

- C1RouteAMomentScalarEdge2620K{d:02d}.lean — the 2620 generator's Edge
  case rendered with the owner's own edge argument, then renamed through
  the 2628 wrapper plus the ScalarEdge-specific renames the wrapper does
  not carry.
- C1RouteAMomentActualEdge2620K{d:02d}.lean — the record-2634 module
  shape with the owner's storedWidth/capturedNodes spellings, the
  cons_val lemma word, and the single-digit decimal bound computed
  EXACTLY from the rounded Expected literals.

`--check` prints the computed bound without writing; owners 0 and 4 must
reproduce the committed bounds (2/10^68 and 5/10^65) before owner 2 (or
any other owner) is generated against this formula. Owner 0 itself has
no K-suffixed pair: its committed originals predate the rename and stay
the reference.
"""
import argparse
import sys
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DEV = ROOT / "ConnesWeilRH" / "Dev"
sys.path.insert(0, str(ROOT / "scripts"))

import generate_moment_diagonal_owner_2628 as wrapper
import generate_moment_scalar_certificate_2620 as scalar_certificate


def cons_val_word(owner_index):
    """Mathlib words for 1-4, project-local digit names for 5-29."""
    if owner_index <= 4:
        return {1: "one", 2: "two", 3: "three", 4: "four"}[owner_index]
    return str(owner_index)


def computed_bound(owner_index):
    """Single-digit decimal >= r^2 * (1/5) * (Expected.1.1 + Expected.2),
    exactly the inequality the ActualEdge module's final norm_num checks."""
    owner = wrapper.owner_data(owner_index)
    center, radius = scalar_certificate.compact_scalar(owner["edge"])[-1]
    prod = owner["radius"] * Fraction(1, 5) * (center + radius)
    # committed convention: minimal k with prod * 10^k >= 1, then the
    # ceiling digit — reproduces owner 0's 2/10^68 and owner 4's 5/10^65
    exponent = 0
    while prod < Fraction(1, 10 ** exponent):
        exponent += 1
    numerator = -((-prod.numerator * 10 ** exponent) // prod.denominator)
    return numerator, exponent, prod


def scalar_edge_source(owner_index):
    owner = wrapper.owner_data(owner_index)
    beta_text = f"((capturedNodes2584 {owner_index}).re * (storedWidth {owner_index} ^ 2))"
    source = scalar_certificate.scalar_source(
        "Edge", "momentEdgeArgument2620", owner["edge"],
        f"-30 / (1 - (9 / 10 : ℝ) ^ 2) + |{beta_text}|",
        "momentEdgeArgument_owner2620", 90)
    source = wrapper.rename_owner_symbols(source, owner_index)
    # renames the wrapper does not carry (it never touches Scalar modules)
    source = source.replace("momentScalarEdge2620",
                            f"momentScalarEdge2620K{owner_index:02d}")
    return source


def actual_edge_source(owner_index, numerator, exponent):
    suffix = f"K{owner_index:02d}"
    word = cons_val_word(owner_index)
    module_source = f"""import ConnesWeilRH.Dev.C1RouteAMomentScalarEdge2620{suffix}
import ConnesWeilRH.Dev.C1RouteAMomentEdgeBound2619

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

theorem actualMomentEntry{owner_index:02d}_bothEdgeCharge_le2620 :
    |(storedWidth {owner_index} ^ 2) *
      ((∫ position in (-1 : ℝ)..(-(9 / 10 : ℝ)),
          realNormalizedMomentIntegrand2618 (storedWidth {owner_index} ^ 2)
            (capturedNodes2584 {owner_index}).re position) +
        (∫ position in (9 / 10 : ℝ)..1,
          realNormalizedMomentIntegrand2618 (storedWidth {owner_index} ^ 2)
            (capturedNodes2584 {owner_index}).re position))| ≤
      ({numerator} : ℝ) / 10 ^ {exponent} := by
  have hradius : 0 < storedWidth {owner_index} ^ 2 := pow_pos (storedWidth_pos {owner_index}) 2
  have hbase := realNormalizedMomentIntegrand2618_edge_integral_bound
    (storedWidth {owner_index} ^ 2) (capturedNodes2584 {owner_index}).re (9 / 10)
    (by norm_num) (by norm_num)
  have hexp := momentScalarEdge2620{suffix}_error
  have hupper := (abs_le.mp hexp).2
  have hbound : momentEdgeUpper2619 (storedWidth {owner_index} ^ 2)
      (capturedNodes2584 {owner_index}).re (9 / 10) ≤
      (momentScalarEdge2620{suffix}Expected.1.1 : ℝ) +
        (momentScalarEdge2620{suffix}Expected.2 : ℝ) := by
    unfold momentEdgeUpper2619
    linarith
  rw [abs_mul, abs_of_pos hradius]
  calc
    _ ≤ (storedWidth {owner_index} ^ 2) *
        (2 * (1 - (9 / 10 : ℝ)) *
          momentEdgeUpper2619 (storedWidth {owner_index} ^ 2)
            (capturedNodes2584 {owner_index}).re (9 / 10)) :=
      mul_le_mul_of_nonneg_left hbase hradius.le
    _ ≤ (storedWidth {owner_index} ^ 2) *
        (2 * (1 - (9 / 10 : ℝ)) *
          ((momentScalarEdge2620{suffix}Expected.1.1 : ℝ) +
            (momentScalarEdge2620{suffix}Expected.2 : ℝ))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hbound (by norm_num)) hradius.le
    _ ≤ _ := by
      norm_num [momentScalarEdge2620{suffix}Expected, storedWidth,
        Matrix.cons_val_{word}, Matrix.cons_val_zero]

end ConnesWeilRH.Dev
"""
    if owner_index >= 5:
        module_source = module_source.replace(
            "import ConnesWeilRH.Dev.C1RouteAMomentEdgeBound2619\n",
            "import ConnesWeilRH.Dev.C1RouteAMomentEdgeBound2619\n"
            "import ConnesWeilRH.Dev.MatrixConsValFamily2637\n")
    return module_source


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--owner-index", type=int, required=True)
    parser.add_argument("--check", action="store_true",
                        help="print the computed bound only (no writes)")
    parser.add_argument("--write", action="store_true")
    arguments = parser.parse_args()
    owner_index = arguments.owner_index
    if owner_index < 0 or owner_index >= 30:
        raise SystemExit("owner index must lie in [0, 29]")
    numerator, exponent, prod = computed_bound(owner_index)
    print(f"owner {owner_index:02d}: bound = {numerator}/10^{exponent} "
          f"(exact product {prod.numerator}/{prod.denominator})")
    if arguments.check:
        return
    if not arguments.write:
        raise SystemExit("nothing to do: pass --check or --write")
    if owner_index == 0:
        raise SystemExit("owner 0 keeps its committed pre-rename edge pair")
    scalar_path = DEV / f"C1RouteAMomentScalarEdge2620K{owner_index:02d}.lean"
    actual_path = DEV / f"C1RouteAMomentActualEdge2620K{owner_index:02d}.lean"
    scalar_path.write_text(scalar_edge_source(owner_index), encoding="utf-8", newline="\n")
    actual_path.write_text(
        actual_edge_source(owner_index, numerator, exponent),
        encoding="utf-8", newline="\n")
    print(scalar_path)
    print(actual_path)


if __name__ == "__main__":
    main()
