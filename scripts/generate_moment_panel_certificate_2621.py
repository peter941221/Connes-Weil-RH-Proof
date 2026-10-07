"""Generate exact degree-32 polynomial certificates for actual panel 094."""
from fractions import Fraction
import hashlib
import json
from pathlib import Path

from generate_moment_scalar_certificate_2620 import compact_scalar, get_data, rational_expr

ROOT = Path(__file__).resolve().parents[1]
DEV = ROOT / "ConnesWeilRH/Dev"


def add(left, right):
    return [(left[index] if index < len(left) else Fraction(0)) +
            (right[index] if index < len(right) else Fraction(0))
            for index in range(max(len(left), len(right)))]


def scale(scalar, coefficients):
    return [scalar * value for value in coefficients]


def multiply(left, right):
    result = []
    for head in reversed(left):
        result = add(scale(head, right), [Fraction(0)] + result)
    return result


def derivative(coefficients):
    result = []
    for index in reversed(range(len(coefficients))):
        result = add(coefficients[index + 1:], [Fraction(0)] + result)
    return result


def evaluate(position, coefficients):
    result = Fraction(0)
    for head in reversed(coefficients):
        result = head + position * result
    return result


def abs_bound(half_width, coefficients):
    return evaluate(half_width, [abs(value) for value in coefficients])


def panel_data():
    owner = get_data()
    beta, center, half_width = owner["beta"], Fraction(9, 200), Fraction(1, 200)
    deficit = [1 - center ** 2, -2 * center, Fraction(-1)]
    denominator = multiply(deficit, deficit)
    numerator = add(scale(beta, denominator), [-60 * center, Fraction(-60)])
    coefficients = [Fraction(1)]
    for order in range(32):
        rhs = sum(numerator[index] * coefficients[order - index]
                  for index in range(min(4, order) + 1))
        lhs = sum(denominator[index] * (order - index + 1) * coefficients[order - index + 1]
                  for index in range(1, min(4, order) + 1))
        coefficients.append((rhs - lhs) / (denominator[0] * (order + 1)))
    primitive = [Fraction(0)] + [value / (index + 1) for index, value in enumerate(coefficients)]
    coefficients.append(Fraction(0))
    if derivative(primitive) != coefficients:
        raise ValueError("primitive derivative does not reconstruct the polynomial")
    residual = add(multiply(denominator, derivative(coefficients)),
                   scale(Fraction(-1), multiply(numerator, coefficients)))
    if any(residual[:32]) or any(residual[37:]):
        raise ValueError("residual is not confined to degrees 32 through 36")
    upper = abs_bound(half_width, residual)
    integral = evaluate(half_width, primitive) - evaluate(-half_width, primitive)
    amplitude, amplitude_error = compact_scalar(owner["phase"])[-1]
    growth, growth_error = compact_scalar(owner["growth"])[-1]
    denominator_lower = (1 - (abs(center) + half_width) ** 2) ** 2
    analytic_charge = ((amplitude + amplitude_error) * (growth + growth_error) *
                       (upper / denominator_lower) * 2 * half_width ** 2)
    charge = owner["radius"] * (analytic_charge + amplitude_error * abs(integral))
    return {**owner, "coefficients": coefficients, "primitive": primitive, "residual": residual,
            "residual_upper": upper, "integral": integral,
            "integral_center": owner["radius"] * amplitude * integral,
            "integral_charge": charge}


def lean_list(values):
    return "[\n    " + ",\n    ".join(rational_expr(value) for value in values) + "]"


def generated_sources(data):
    table = f"""import ConnesWeilRH.Dev.C1RouteARationalPolynomial2621
import ConnesWeilRH.Dev.C1RouteAMomentScalarAmplitude2620Panel094
import ConnesWeilRH.Dev.C1RouteAMomentScalarGrowth2620Panel094

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace ConnesWeilRH.Dev

def momentPanelDeficit2621 : List ℚ := [1 - (9 / 200) ^ 2, -2 * (9 / 200), -1]

def momentPanelDenominator2621 : List ℚ :=
  polynomialMul2621 momentPanelDeficit2621 momentPanelDeficit2621

def momentPanelNumerator2621 : List ℚ := polynomialAdd2621
  (polynomialScale2621 momentBeta2620 momentPanelDenominator2621)
  (polynomialScale2621 (-60) [9 / 200, 1])

def momentPanelPolynomial2621 : List ℚ := {lean_list(data['coefficients'])}

def momentPanelPrimitive2621 : List ℚ := {lean_list(data['primitive'])}

def momentPanelResidual2621 : List ℚ := {lean_list(data['residual'])}

def momentPanelResidualUpper2621 : ℚ := {rational_expr(data['residual_upper'])}

def momentPanelIntegral2621 : ℚ := {rational_expr(data['integral'])}

def momentPanelIntegralCenter2621 : ℚ := {rational_expr(data['integral_center'])}

def momentPanelIntegralCharge2621 : ℚ := {rational_expr(data['integral_charge'])}

def momentPanelAnalyticCharge2621 : ℚ :=
  (momentScalarAmplitude2620Expected.1.1 + momentScalarAmplitude2620Expected.2) *
  (momentScalarGrowth2620Expected.1.1 + momentScalarGrowth2620Expected.2) *
  (momentPanelResidualUpper2621 / (1 - (|9 / 200| + 1 / 200) ^ 2) ^ 2) *
  (2 * (1 / 200) ^ 2)

theorem momentPanelPrimitive_replay2621 :
    polynomialDerivative2621 momentPanelPrimitive2621 = momentPanelPolynomial2621 := by
  decide +kernel

theorem momentPanelResidual_replay2621 :
    polynomialAdd2621
      (polynomialMul2621 momentPanelDenominator2621
        (polynomialDerivative2621 momentPanelPolynomial2621))
      (polynomialScale2621 (-1)
        (polynomialMul2621 momentPanelNumerator2621 momentPanelPolynomial2621)) =
      momentPanelResidual2621 := by
  decide +kernel

theorem momentPanelResidualUpper_replay2621 :
    polynomialAbsBound2621 (1 / 200) momentPanelResidual2621 = momentPanelResidualUpper2621 := by
  decide +kernel

theorem momentPanelIntegral_replay2621 :
    polynomialEvalRat2621 (1 / 200) momentPanelPrimitive2621 -
      polynomialEvalRat2621 (-1 / 200) momentPanelPrimitive2621 = momentPanelIntegral2621 := by
  decide +kernel

theorem momentPanelCenter_replay2621 :
    momentRadius2620 * momentScalarAmplitude2620Expected.1.1 * momentPanelIntegral2621 =
      momentPanelIntegralCenter2621 := by
  decide +kernel

theorem momentPanelCharge_replay2621 :
    momentRadius2620 * (momentPanelAnalyticCharge2621 +
      momentScalarAmplitude2620Expected.2 * |momentPanelIntegral2621|) =
      momentPanelIntegralCharge2621 := by
  decide +kernel

theorem momentPanelCharge_le2621 : momentPanelIntegralCharge2621 ≤ 1 / 10 ^ 82 := by
  decide +kernel

theorem momentPanelResidualUpper_nonneg2621 : 0 ≤ momentPanelResidualUpper2621 := by
  decide +kernel

theorem momentPanelResidual_low_zero2621 :
    momentPanelResidual2621.take 32 = List.replicate 32 (0 : ℚ) := by
  decide +kernel

theorem momentPanelResidual_tail_zero2621 :
    momentPanelResidual2621.drop 37 = [0] := by
  decide +kernel

end ConnesWeilRH.Dev
"""
    helper = ("polynomialEval_add2621", "polynomialEval_scale2621", "polynomialEval_mul2621",
              "polynomialEval_hasDerivAt2621", "polynomialEval_cast2621",
              "polynomialAbsBound_nonneg2621", "polynomialEval_abs_le2621", "polynomialEval_integral2621")
    replay = ("momentPanelPrimitive_replay2621", "momentPanelResidual_replay2621",
              "momentPanelResidualUpper_replay2621", "momentPanelIntegral_replay2621",
              "momentPanelCenter_replay2621", "momentPanelCharge_replay2621",
              "momentPanelCharge_le2621", "momentPanelResidualUpper_nonneg2621",
              "momentPanelResidual_low_zero2621", "momentPanelResidual_tail_zero2621")
    consumer = ("momentPanelDenominator_eval2621", "momentPanelNumerator_eval2621",
                "momentPanelResidual_eval2621", "momentPanelResidual_bound2621",
                "momentPanelPolynomial_integral2621", "momentPanelPhase_error2621",
                "actualMomentPanel094_integral_certificate2621", "actualMomentPanel094_integral_error_le2621")
    audit = "import ConnesWeilRH.Dev.C1RouteAMomentActualPanel2621Panel094\n\n" + "\n".join(
        f"#print axioms ConnesWeilRH.Dev.{name}" for name in helper + replay + consumer) + "\n"
    return {"C1RouteAMomentPanelTable2621Panel094.lean": table,
            "C1RouteAMomentPanelAudit2621.lean": audit}


def payload_data(data):
    return {"record": 2621, "entry": [0, 0], "panel": 94, "degree": 32,
               "center_exact": "9/200", "half_width_exact": "1/200",
               "capture_sha256": data["capture_sha256"], "witness_sha256": data["witness_sha256"],
               "generator_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
               "scalar_generator_sha256": hashlib.sha256(
                   ROOT.joinpath("scripts/generate_moment_scalar_certificate_2620.py").read_bytes()).hexdigest(),
               "data": {key: [str(value) for value in data[key]] if isinstance(data[key], list)
                        else str(data[key]) for key in ("coefficients", "primitive", "residual",
                            "residual_upper", "integral", "integral_center", "integral_charge")},
               "lean_verified": False, "actual_entry_containment_lean_verified": False,
               "producer_go": False, "rh_claim": False}


def main():
    data = panel_data()
    for filename, source in generated_sources(data).items():
        (DEV / filename).write_text(source, encoding="utf-8", newline="\n")
    ROOT.joinpath("results/2621_moment_panel_payload.json").write_text(
        json.dumps(payload_data(data), indent=2) + "\n", encoding="utf-8", newline="\n")
    print(f"generated panel094: residual upper ~{float(data['residual_upper']):.6e}, "
          f"physical integral charge ~{float(data['integral_charge']):.6e}", flush=True)


if __name__ == "__main__":
    main()
