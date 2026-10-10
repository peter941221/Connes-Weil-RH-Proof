"""Generate the complex panel-table Lean module for the off-diagonal pilot.

Record 2648. Brick 3 of the record-2624 GO route: the first complex panel
table, instantiating the record-2647 generic layer (complexPolyEval2647,
complexPolyAbsBound2647) with the exact rational data of one panel of the
pilot entry (0, 3).

The panel data mirrors scripts/offdiagonal_residual_pricing_2624.py line for
line (deficit -> real denominator via the 2622 real multiply, complex
numerator N = (beta + i*psi) * D - 60*(center + t), degree-55 recurrence,
five residual slots, |re| + |im| modulus bound); every emitted table is then
regression-checked against build_complex_panel itself, so the Lean tables
are the byte-for-byte objects the pricing run verified.

Every Lean theorem in the emitted module is a `decide +kernel` replay of a
concrete list identity, mirroring the real panel tables of records 2621-2622:
primitive derivative, D P' - N P residual (with take/drop zero-slot checks),
|re|+|im| residual upper, and the two integral components. No analytic
containment is emitted here; that is the next brick.

Scope: data layer only. No off-diagonal claim, no Producer GO, no SourceRH,
no RH.
"""

import hashlib
import json
from fractions import Fraction
from pathlib import Path
import sys

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)

sys.path.insert(0, str(Path(__file__).resolve().parent))

import generate_moment_panel_batch_2622 as _panel
from offdiagonal_residual_pricing_2624 import (
    HALF_WIDTH, ROW, build_complex_panel, column_parameters, complex_multiply,
    convolve, panel_center,
)

ROOT = Path(__file__).resolve().parents[1]
DEGREE = 55
WORST_PANEL = 109
RECORD = 2648
TAG = f"{WORST_PANEL:03d}"


def q(value):
    if value.denominator == 1:
        return f"({value.numerator} : ℚ)"
    return f"(({value.numerator} : ℚ) / {value.denominator})"


def pair(value):
    return f"({q(value[0])}, {q(value[1])})"


def panel_tables(beta, psi, center, degree):
    """Verbatim mirror of offdiagonal_residual_pricing_2624.build_complex_panel,
    returning every intermediate so the Lean tables can be emitted."""
    deficit = [1 - center ** 2, -2 * center, Fraction(-1)]
    denominator = _panel.multiply(deficit, deficit)
    numerator = [(beta * value, psi * value) for value in denominator]
    numerator[0] = (numerator[0][0] - 60 * center, numerator[0][1])
    numerator[1] = (numerator[1][0] - 60, numerator[1][1])
    coefficients = [(Fraction(1), Fraction(0))]
    for order in range(degree):
        rhs = (Fraction(0), Fraction(0))
        for index in range(min(4, order) + 1):
            product = complex_multiply(numerator[index], coefficients[order - index])
            rhs = (rhs[0] + product[0], rhs[1] + product[1])
        lhs = (Fraction(0), Fraction(0))
        for index in range(1, min(4, order) + 1):
            factor = denominator[index] * (order - index + 1)
            term = coefficients[order - index + 1]
            lhs = (lhs[0] + factor * term[0], lhs[1] + factor * term[1])
        scale = denominator[0] * (order + 1)
        coefficients.append(((rhs[0] - lhs[0]) / scale, (rhs[1] - lhs[1]) / scale))
    # the emitted polynomial carries one trailing zero slot so the Lean
    # derivative (length-preserving) of primitive and polynomial have matching
    # lengths (record-2621 house convention, table ends with ((0 : Q) / 1))
    coefficients_emitted = coefficients + [(Fraction(0), Fraction(0))]
    derivative = [(index * value[0], index * value[1])
                  for index, value in enumerate(coefficients_emitted)][1:]
    product_ds = convolve([(value, Fraction(0)) for value in denominator], derivative)
    product_ns = convolve(numerator, coefficients_emitted)
    residual = []
    for index in range(max(len(product_ds), len(product_ns))):
        ds = product_ds[index] if index < len(product_ds) else (Fraction(0), Fraction(0))
        ns = product_ns[index] if index < len(product_ns) else (Fraction(0), Fraction(0))
        residual.append((ds[0] - ns[0], ds[1] - ns[1]))
    zero = (Fraction(0), Fraction(0))
    if any(value != zero for value in residual[:degree]):
        raise RuntimeError("exact low-order complex residual identity failed")
    if any(value != zero for value in residual[degree + 5:]):
        raise RuntimeError("complex residual leaves more than five slots")
    modulus_bound = sum((abs(value[0]) + abs(value[1])) * HALF_WIDTH ** index
                        for index, value in enumerate(residual))
    primitive = [(Fraction(0), Fraction(0))]
    for index, value in enumerate(coefficients):
        primitive.append((value[0] / (index + 1), value[1] / (index + 1)))
    integral = (Fraction(0), Fraction(0))
    for index, value in enumerate(primitive):
        if index % 2 == 1:
            weight = 2 * HALF_WIDTH ** index
            integral = (integral[0] + value[0] * weight,
                        integral[1] + value[1] * weight)
    return {"deficit": deficit, "denominator": denominator, "numerator": numerator,
            "coefficients": coefficients_emitted, "primitive": primitive,
            "residual": residual, "modulus_bound": modulus_bound,
            "integral": integral}


def build_module(tables):
    beta, psi = tables["beta"], tables["psi"]
    center, degree = tables["center"], DEGREE
    deficit = tables["deficit"]
    numerator, coefficients = tables["numerator"], tables["coefficients"]
    primitive, residual = tables["primitive"], tables["residual"]
    deficit_body = ",\n".join(f"  {pair((value, Fraction(0)))}" for value in deficit)
    numerator_body = ",\n".join(f"  {pair(value)}" for value in numerator)
    polynomial_body = ",\n".join(f"  {pair(value)}" for value in coefficients)
    primitive_body = ",\n".join(f"  {pair(value)}" for value in primitive)
    residual_body = ",\n".join(f"  {pair(value)}" for value in residual)
    return f"""import ConnesWeilRH.Dev.C1RouteAComplexResidualStability2647

-- Generated exact-rational tables: the scalar and slot lines exceed the
-- 100-character style limit by construction.
set_option linter.style.longLine false

namespace ConnesWeilRH.Dev

/-!
# Complex panel table, pilot entry (0, 3), panel {TAG} (record {RECORD})

Exact rational data of one panel of the record-2624 GO route: center
{center}, half width 1/200, degree {degree}, complex numerator
N(t) = (beta + i*psi) * D(t) - 60 * (center + t). The tables are emitted by
scripts/generate_complex_panel_table_2648.py from the record-2624 pricing
pipeline and regression-checked against `build_complex_panel`; every theorem
is a `decide +kernel` replay of a concrete list identity against the
record-2647 generic layer. Data layer only: no analytic containment, no
off-diagonal claim.
-/

def complexPanelBeta2648P{TAG} : ℚ := {q(beta)}

def complexPanelPsi2648P{TAG} : ℚ := {q(psi)}

def complexPanelCenter2648P{TAG} : ℚ := {q(center)}

def complexPanelDeficit2648P{TAG} : List RatPair2542 := [
{deficit_body}]

def complexPanelNumerator2648P{TAG} : List RatPair2542 := [
{numerator_body}]

def complexPanelPolynomial2648P{TAG} : List RatPair2542 := [
{polynomial_body}]

def complexPanelPrimitive2648P{TAG} : List RatPair2542 := [
{primitive_body}]

def complexPanelResidual2648P{TAG} : List RatPair2542 := [
{residual_body}]

def complexPanelResidualUpper2648P{TAG} : ℚ := {q(tables["modulus_bound"])}

def complexPanelIntegral2648P{TAG} : RatPair2542 := {pair(tables["integral"])}

set_option maxHeartbeats 2000000 in
-- exact-rational decide replay at degree 55 needs the 2621 heartbeat ceiling
theorem complexPanelPrimitive_replay2648P{TAG} :
    complexPolyDerivative2647 complexPanelPrimitive2648P{TAG} =
      complexPanelPolynomial2648P{TAG} := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- exact-rational decide replay at degree 55 needs the 2621 heartbeat ceiling
theorem complexPanelResidual_replay2648P{TAG} :
    complexPolyAdd2647
      (complexPolyMul2647
        (complexPolyMul2647 complexPanelDeficit2648P{TAG}
          complexPanelDeficit2648P{TAG})
        (complexPolyDerivative2647 complexPanelPolynomial2648P{TAG}))
      (complexPolyScale2647 (-1, 0)
        (complexPolyMul2647 complexPanelNumerator2648P{TAG}
          complexPanelPolynomial2648P{TAG})) =
      complexPanelResidual2648P{TAG} := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- exact-rational decide replay at degree 55 needs the 2621 heartbeat ceiling
theorem complexPanelResidual_low_zero2648P{TAG} :
    complexPanelResidual2648P{TAG}.take {degree} =
      List.replicate {degree} (0, 0) := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- exact-rational decide replay at degree 55 needs the 2621 heartbeat ceiling
theorem complexPanelResidual_tail_zero2648P{TAG} :
    complexPanelResidual2648P{TAG}.drop {degree + 5} = [(0, 0)] := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- exact-rational decide replay at degree 55 needs the 2621 heartbeat ceiling
theorem complexPanelResidualUpper_replay2648P{TAG} :
    complexPolyAbsBound2647 (1 / 200) complexPanelResidual2648P{TAG} =
      complexPanelResidualUpper2648P{TAG} := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- exact-rational decide replay at degree 55 needs the 2621 heartbeat ceiling
theorem complexPanelResidualUpper_nonneg2648P{TAG} :
    0 ≤ complexPanelResidualUpper2648P{TAG} := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- exact-rational decide replay at degree 55 needs the 2621 heartbeat ceiling
theorem complexPanelIntegral_re2648P{TAG} :
    (complexPolyEvalRat2647 (1 / 200) complexPanelPrimitive2648P{TAG}).1 -
      (complexPolyEvalRat2647 (-(1 / 200)) complexPanelPrimitive2648P{TAG}).1 =
      complexPanelIntegral2648P{TAG}.1 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- exact-rational decide replay at degree 55 needs the 2621 heartbeat ceiling
theorem complexPanelIntegral_im2648P{TAG} :
    (complexPolyEvalRat2647 (1 / 200) complexPanelPrimitive2648P{TAG}).2 -
      (complexPolyEvalRat2647 (-(1 / 200)) complexPanelPrimitive2648P{TAG}).2 =
      complexPanelIntegral2648P{TAG}.2 := by
  decide +kernel

end ConnesWeilRH.Dev
"""


def main():
    capture = json.loads(
        (ROOT / "results/2275_gap_owner_audit.json").read_text())["owner_capture"]
    pilot = column_parameters(capture, 3)
    center = panel_center(WORST_PANEL)
    tables = panel_tables(pilot["beta"], pilot["psi"], center, DEGREE)
    tables["beta"], tables["psi"], tables["center"] = \
        pilot["beta"], pilot["psi"], center

    # regression against the record-2624 pricing pipeline itself
    reference = build_complex_panel(pilot["beta"], pilot["psi"], center, DEGREE)
    assert tables["modulus_bound"] == reference["residual_modulus_upper"], \
        "residual upper diverges from the 2624 pipeline"
    assert tables["integral"] == reference["integral"], \
        "integral diverges from the 2624 pipeline"

    # regression against the committed 2624 payload: panel 109 must be the
    # recorded worst panel at degree 55
    payload = json.loads(
        (ROOT / "results/2624_offdiagonal_pricing.json").read_text())
    ladder55 = [rung for rung in payload["degree_ladder"]
                if rung["degree"] == DEGREE][0]
    assert ladder55["worst_panel"] == WORST_PANEL, \
        "panel 109 is not the recorded worst panel at degree 55"

    out = ROOT / f"ConnesWeilRH/Dev/C1RouteAComplexPanelTable{RECORD}P{TAG}.lean"
    out.write_text(build_module(tables), encoding="utf-8", newline="\n")

    slot_mag = max((abs(value[0]) + abs(value[1]))
                   for value in tables["residual"][DEGREE:DEGREE + 5])
    summary = {
        "record": RECORD, "panel": WORST_PANEL, "degree": DEGREE,
        "entry": [ROW, 3],
        "beta_exact": str(tables["beta"]), "psi_exact": str(tables["psi"]),
        "center_exact": str(center),
        "coefficient_count": len(tables["coefficients"]),
        "residual_length": len(tables["residual"]),
        "residual_slot_max_abs_exact": str(slot_mag),
        "residual_upper_exact": str(tables["modulus_bound"]),
        "integral_re_exact": str(tables["integral"][0]),
        "integral_im_exact": str(tables["integral"][1]),
        "generator_sha256":
            hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "module": out.name,
        "selftest": "2624 build_complex_panel regression + worst-panel "
                    "payload check passed",
    }
    (ROOT / f"results/{RECORD}_complex_panel_table.json").write_text(
        json.dumps(summary, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(f"wrote {out.name}: {len(tables['coefficients'])} coefficients, "
          f"residual_upper ~{float(tables['modulus_bound']):.6e}, "
          f"integral ~({float(tables['integral'][0]):.6e}, "
          f"{float(tables['integral'][1]):.6e})")


if __name__ == "__main__":
    main()
