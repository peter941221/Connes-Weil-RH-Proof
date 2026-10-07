"""Generate parameterized actual-panel certificates for a batch of panels.

Record 2622. Each panel of the committed 180-panel partition receives the
record-2621 certificate shape: panel scalar exponentials, an exact degree-32
rational polynomial table replayed by the kernel, and the actual integral
consumer. The template reproduces the committed panel094 modules byte for
byte when instantiated at the record-2621 parameters; the selftest gates
that fidelity before any new panel is emitted.

Every generated payload and module is written with explicit LF newlines.
A panel whose charge exceeds 1/10^82, whose scalar radius misses its bound,
or whose residual leaves the five slots 32..36 aborts generation.
"""
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import sys

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)

from generate_moment_scalar_certificate_2620 import compact_scalar, get_data, rational_expr
from generate_moment_panel_certificate_2621 import (
    add,
    abs_bound,
    derivative,
    evaluate,
    multiply,
    scale,
)

ROOT = Path(__file__).resolve().parents[1]
DEV = ROOT / "ConnesWeilRH/Dev"
HALF_WIDTH = Fraction(1, 200)
DEGREE = 32
PARTITION_SAFETY = 100


def display_digits(radius):
    """Largest decimal exponent d with radius <= 1/10^d (the committed
    engine's 320/400-bit directed rounding gives panel-dependent radii)."""
    if radius <= 0:
        raise ValueError("radius must be positive")
    digits = 0
    power = Fraction(1)
    while radius <= power / 10:
        power /= 10
        digits += 1
    return digits


def panel_center(index):
    if not 0 <= index < 180:
        raise ValueError("panel index must lie in [0, 179]")
    return Fraction(-9, 10) + (2 * index + 1) * HALF_WIDTH


def lean_rat(value):
    value = Fraction(value)
    if value.denominator == 1:
        return f"({value.numerator})"
    return f"({value.numerator} / {value.denominator})"


def lean_interval_literal(value):
    """Interval endpoint literal for the actual-panel theorem statements.

    A negative endpoint must emit as -(p / q): (-p / q) elaborates as
    (Neg p) / q, while the norm_num products inside the proof carry
    Neg (p / q), and the two shapes are not Eq.mp-compatible (caught by
    the compiler on the first negative-center panel, record 2625).
    Positive endpoints keep the plain lean_rat shape, so the committed
    positive-center panels regenerate byte-identically.
    """
    value = Fraction(value)
    if value >= 0:
        return lean_rat(value)
    return f"-{lean_rat(-value)}"


def lean_list(values):
    return "[\n    " + ",\n    ".join(rational_expr(value) for value in values) + "]"


def panel_data(index, owner):
    beta, center = owner["beta"], panel_center(index)
    half_width = HALF_WIDTH
    deficit = [1 - center ** 2, -2 * center, Fraction(-1)]
    denominator = multiply(deficit, deficit)
    numerator = add(scale(beta, denominator), [-60 * center, Fraction(-60)])
    coefficients = [Fraction(1)]
    for order in range(DEGREE):
        rhs = sum(numerator[index] * coefficients[order - index]
                  for index in range(min(4, order) + 1))
        lhs = sum(denominator[index] * (order - index + 1) * coefficients[order - index + 1]
                  for index in range(1, min(4, order) + 1))
        coefficients.append((rhs - lhs) / (denominator[0] * (order + 1)))
    primitive = [Fraction(0)] + [value / (index + 1) for index, value in enumerate(coefficients)]
    coefficients.append(Fraction(0))
    if derivative(primitive) != coefficients:
        raise ValueError(f"panel {index}: primitive derivative does not reconstruct")
    residual = add(multiply(denominator, derivative(coefficients)),
                   scale(Fraction(-1), multiply(numerator, coefficients)))
    if any(residual[:DEGREE]) or any(residual[DEGREE + 5:]):
        raise ValueError(f"panel {index}: residual is not confined to degrees 32 through 36")
    upper = abs_bound(half_width, residual)
    integral = evaluate(half_width, primitive) - evaluate(-half_width, primitive)
    edge = abs(center) + half_width
    denominator_lower = (1 - edge ** 2) ** 2
    phase = Fraction(-30) / (1 - center ** 2) + beta * center
    growth = 2 * (abs(beta) + 60 * edge / denominator_lower) * half_width
    amplitude_states = compact_scalar(phase)
    amplitude_center, amplitude_radius = amplitude_states[-1]
    growth_states = compact_scalar(growth)
    growth_center, growth_radius = growth_states[-1]
    amplitude_digits = display_digits(amplitude_radius)
    growth_digits = display_digits(growth_radius)
    analytic_charge = ((amplitude_center + amplitude_radius) *
                       (growth_center + growth_radius) *
                       (upper / denominator_lower) * 2 * half_width ** 2)
    charge = owner["radius"] * (analytic_charge + amplitude_radius * abs(integral))
    return {"index": index, "center": center, "beta": beta, "radius": owner["radius"],
            "coefficients": coefficients, "primitive": primitive, "residual": residual,
            "residual_upper": upper, "integral": integral,
            "phase": phase, "growth": growth,
            "amplitude_center": amplitude_center, "amplitude_radius": amplitude_radius,
            "amplitude_digits": amplitude_digits,
            "growth_center": growth_center, "growth_radius": growth_radius,
            "growth_digits": growth_digits,
            "integral_center": owner["radius"] * amplitude_center * integral,
            "integral_charge": charge,
            "charge_digits": display_digits(charge)}


def scalar_sources(data):
    """Panel scalar module: owner phases plus two scaling-and-squaring certificates."""
    tag = f"{data['index']:03d}"
    year = f"2622P{tag}"
    beta = "((capturedNodes2584 0).re * (storedWidth 0 ^ 2))"
    center_literal = lean_rat(data["center"])
    return f"""import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase{year} : ℚ := {rational_expr(data['phase'])}

def momentPanelGrowth{year} : ℚ := {rational_expr(data['growth'])}

theorem momentPanelPhase_owner{year} :
    (momentPanelPhase{year} : ℝ) = momentPhase2619 {beta} {center_literal} 0 := by
  norm_num [momentPanelPhase{year}, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner{year} :
    (momentPanelGrowth{year} : ℝ) = 2 * momentPhaseSlopeUpper2619 {beta}
      {center_literal} {lean_rat(HALF_WIDTH)} * {lean_rat(HALF_WIDTH)} := by
  norm_num [momentPanelGrowth{year}, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp{year}Input : RatPair2542 := (momentPanelPhase{year} / (2 : ℚ) ^ 20, 0)

def momentScalarAmp{year}Expected : RatState2542 :=
  (({rational_expr(data['amplitude_center'])}, 0), {rational_expr(data['amplitude_radius'])})

theorem momentScalarAmp{year}_replay :
    compactExp2620 momentScalarAmp{year}Input 20 = momentScalarAmp{year}Expected := by
  decide +kernel

theorem momentScalarAmp{year}_error :
    |Real.exp (momentPhase2619 {beta} {center_literal} 0) -
      (momentScalarAmp{year}Expected.1.1 : ℝ)| ≤
      (momentScalarAmp{year}Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase{year} / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase{year}]
  have h := compactExp_real_error2620 momentPanelPhase{year} 20 hsmall
  change |Real.exp (momentPanelPhase{year} : ℝ) -
    ((compactExp2620 momentScalarAmp{year}Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp{year}Input 20).2 : ℝ) at h
  rw [momentScalarAmp{year}_replay] at h
  simpa only [momentPanelPhase_owner{year}] using h

theorem momentScalarAmp{year}_radius_le :
    (momentScalarAmp{year}Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ {data['amplitude_digits']} := by
  norm_num [momentScalarAmp{year}Expected]

def momentScalarGrow{year}Input : RatPair2542 := (momentPanelGrowth{year} / (2 : ℚ) ^ 20, 0)

def momentScalarGrow{year}Expected : RatState2542 :=
  (({rational_expr(data['growth_center'])}, 0), {rational_expr(data['growth_radius'])})

theorem momentScalarGrow{year}_replay :
    compactExp2620 momentScalarGrow{year}Input 20 = momentScalarGrow{year}Expected := by
  decide +kernel

theorem momentScalarGrow{year}_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 {beta} {center_literal} {lean_rat(HALF_WIDTH)} *
      {lean_rat(HALF_WIDTH)}) -
      (momentScalarGrow{year}Expected.1.1 : ℝ)| ≤
      (momentScalarGrow{year}Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth{year} / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth{year}]
  have h := compactExp_real_error2620 momentPanelGrowth{year} 20 hsmall
  change |Real.exp (momentPanelGrowth{year} : ℝ) -
    ((compactExp2620 momentScalarGrow{year}Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow{year}Input 20).2 : ℝ) at h
  rw [momentScalarGrow{year}_replay] at h
  simpa only [momentPanelGrowth_owner{year}] using h

theorem momentScalarGrow{year}_radius_le :
    (momentScalarGrow{year}Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ {data['growth_digits']} := by
  norm_num [momentScalarGrow{year}Expected]

end ConnesWeilRH.Dev
"""


def table_sources(data):
    """Panel table module: exact rational lists replayed by decide + kernel."""
    tag = f"{data['index']:03d}"
    year = f"2622P{tag}"
    center_literal = lean_rat(data["center"])
    half_literal = lean_rat(HALF_WIDTH)
    return f"""import ConnesWeilRH.Dev.C1RouteARationalPolynomial2621
import ConnesWeilRH.Dev.C1RouteAMomentPanelScalars2622Panel{tag}

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace ConnesWeilRH.Dev

def momentPanelDeficit{year} : List ℚ := [1 - {center_literal} ^ 2, -2 * {center_literal}, -1]

def momentPanelDenominator{year} : List ℚ :=
  polynomialMul2621 momentPanelDeficit{year} momentPanelDeficit{year}

def momentPanelNumerator{year} : List ℚ := polynomialAdd2621
  (polynomialScale2621 momentBeta2620 momentPanelDenominator{year})
  (polynomialScale2621 (-60) [{center_literal.removeprefix('(').removesuffix(')')}, 1])

def momentPanelPolynomial{year} : List ℚ := {lean_list(data['coefficients'])}

def momentPanelPrimitive{year} : List ℚ := {lean_list(data['primitive'])}

def momentPanelResidual{year} : List ℚ := {lean_list(data['residual'])}

def momentPanelResidualUpper{year} : ℚ := {rational_expr(data['residual_upper'])}

def momentPanelIntegral{year} : ℚ := {rational_expr(data['integral'])}

def momentPanelIntegralCenter{year} : ℚ := {rational_expr(data['integral_center'])}

def momentPanelIntegralCharge{year} : ℚ := {rational_expr(data['integral_charge'])}

def momentPanelAnalyticCharge{year} : ℚ :=
  (momentScalarAmp{year}Expected.1.1 + momentScalarAmp{year}Expected.2) *
  (momentScalarGrow{year}Expected.1.1 + momentScalarGrow{year}Expected.2) *
  (momentPanelResidualUpper{year} / (1 - (|{center_literal}| + {half_literal}) ^ 2) ^ 2) *
  (2 * {half_literal} ^ 2)

theorem momentPanelPrimitive_replay{year} :
    polynomialDerivative2621 momentPanelPrimitive{year} = momentPanelPolynomial{year} := by
  decide +kernel

theorem momentPanelResidual_replay{year} :
    polynomialAdd2621
      (polynomialMul2621 momentPanelDenominator{year}
        (polynomialDerivative2621 momentPanelPolynomial{year}))
      (polynomialScale2621 (-1)
        (polynomialMul2621 momentPanelNumerator{year} momentPanelPolynomial{year})) =
      momentPanelResidual{year} := by
  decide +kernel

theorem momentPanelResidualUpper_replay{year} :
    polynomialAbsBound2621 {half_literal} momentPanelResidual{year} =
      momentPanelResidualUpper{year} := by
  decide +kernel

theorem momentPanelIntegral_replay{year} :
    polynomialEvalRat2621 {half_literal} momentPanelPrimitive{year} -
      polynomialEvalRat2621 (-{half_literal.removeprefix('(')} momentPanelPrimitive{year} =
      momentPanelIntegral{year} := by
  decide +kernel

theorem momentPanelCenter_replay{year} :
    momentRadius2620 * momentScalarAmp{year}Expected.1.1 * momentPanelIntegral{year} =
      momentPanelIntegralCenter{year} := by
  decide +kernel

theorem momentPanelCharge_replay{year} :
    momentRadius2620 * (momentPanelAnalyticCharge{year} +
      momentScalarAmp{year}Expected.2 * |momentPanelIntegral{year}|) =
      momentPanelIntegralCharge{year} := by
  decide +kernel

theorem momentPanelCharge_le{year} :
    momentPanelIntegralCharge{year} ≤ 1 / 10 ^ {data['charge_digits']} := by
  decide +kernel

theorem momentPanelResidualUpper_nonneg{year} : 0 ≤ momentPanelResidualUpper{year} := by
  decide +kernel

theorem momentPanelResidual_low_zero{year} :
    momentPanelResidual{year}.take {DEGREE} = List.replicate {DEGREE} (0 : ℚ) := by
  decide +kernel

theorem momentPanelResidual_tail_zero{year} :
    momentPanelResidual{year}.drop {DEGREE + 5} = [0] := by
  decide +kernel

end ConnesWeilRH.Dev
"""


def consumer_sources(data):
    """Actual integral consumer; the parameterized record-2621 proof shape."""
    tag = f"{data['index']:03d}"
    year = f"2622P{tag}"
    center_literal = lean_rat(data["center"])
    half_literal = lean_rat(HALF_WIDTH)
    # Negative centers leave Rat.cast (-p) residues after the cast_div push;
    # only those panels need Rat.cast_neg in the charge simplifier set.
    cast_neg = ", Rat.cast_neg" if data["center"] < 0 else ""
    return f"""import ConnesWeilRH.Dev.C1RouteAMomentPanelTable2622Panel{tag}

namespace ConnesWeilRH.Dev

open Set
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

theorem momentPanelDenominator_eval{year} (position : ℝ) :
    polynomialEval2621 momentPanelDenominator{year} position =
      (1 - ({center_literal} + position) ^ 2) ^ 2 := by
  rw [momentPanelDenominator{year}, polynomialEval_mul2621]
  norm_num [momentPanelDeficit{year}, polynomialEval2621]
  ring

theorem momentPanelNumerator_eval{year} (position : ℝ) :
    polynomialEval2621 momentPanelNumerator{year} position =
      (momentBeta2620 : ℝ) * (1 - ({center_literal} + position) ^ 2) ^ 2 -
        60 * ({center_literal} + position) := by
  rw [momentPanelNumerator{year}, polynomialEval_add2621, polynomialEval_scale2621,
    polynomialEval_scale2621, momentPanelDenominator_eval{year}]
  norm_num [polynomialEval2621]
  ring

theorem momentPanelResidual_eval{year} (position : ℝ) :
    polynomialEval2621 momentPanelResidual{year} position =
      momentPolynomialResidual2619 (momentBeta2620 : ℝ) {center_literal}
        (polynomialEval2621 momentPanelPolynomial{year})
        (polynomialEval2621 (polynomialDerivative2621 momentPanelPolynomial{year})) position := by
  rw [← momentPanelResidual_replay{year}, polynomialEval_add2621, polynomialEval_mul2621,
    polynomialEval_scale2621, polynomialEval_mul2621, momentPanelDenominator_eval{year},
    momentPanelNumerator_eval{year}]
  simp only [momentPolynomialResidual2619, Rat.cast_neg, Rat.cast_one]
  ring

theorem momentPanelResidual_bound{year} (position : ℝ)
    (hposition : position ∈ Icc (-{half_literal}) {half_literal}) :
    |momentPolynomialResidual2619 (momentBeta2620 : ℝ) {center_literal}
      (polynomialEval2621 momentPanelPolynomial{year})
      (polynomialEval2621 (polynomialDerivative2621 momentPanelPolynomial{year})) position| ≤
      (momentPanelResidualUpper{year} : ℝ) := by
  rw [← momentPanelResidual_eval{year}, ← momentPanelResidualUpper_replay{year}]
  apply polynomialEval_abs_le2621 _ {half_literal} (by norm_num)
  simpa using abs_le.mpr hposition

theorem momentPanelPolynomial_integral{year} :
    (∫ position in (-{half_literal})..{half_literal},
      polynomialEval2621 momentPanelPolynomial{year} position) = (momentPanelIntegral{year} : ℝ) := by
  have h := polynomialEval_integral2621 momentPanelPolynomial{year} momentPanelPrimitive{year}
    momentPanelPrimitive_replay{year} (-{half_literal.removeprefix('(')} {half_literal}
  rw [momentPanelIntegral_replay{year}] at h
  convert h using 1
  norm_num

theorem momentPanelPhase_error{year} :
    |(∫ position in (-{half_literal})..{half_literal},
        Real.exp (momentPhase2619 (momentBeta2620 : ℝ) {center_literal} position)) -
      Real.exp (momentPhase2619 (momentBeta2620 : ℝ) {center_literal} 0) *
        (momentPanelIntegral{year} : ℝ)| ≤ (momentPanelAnalyticCharge{year} : ℝ) := by
  have hbase := momentPhase_integral_error_of_polynomialResidual2619
    (momentBeta2620 : ℝ) {center_literal} (polynomialEval2621 momentPanelPolynomial{year})
    (polynomialEval2621 (polynomialDerivative2621 momentPanelPolynomial{year})) {half_literal}
    (momentPanelResidualUpper{year} : ℝ) (by norm_num) (by norm_num)
    (Rat.cast_nonneg.mpr momentPanelResidualUpper_nonneg{year})
    (by norm_num [momentPanelPolynomial{year}, polynomialEval2621])
    (fun position _ => polynomialEval_hasDerivAt2621 _ position)
    momentPanelResidual_bound{year}
  rw [momentPanelPolynomial_integral{year}] at hbase
  have hamplitude := (abs_le.mp momentScalarAmp{year}_error).2
  have hgrowth := (abs_le.mp momentScalarGrow{year}_error).2
  rw [← momentBeta_owner2620] at hamplitude hgrowth
  have hamplitudeUpper : Real.exp
      (momentPhase2619 (momentBeta2620 : ℝ) {center_literal} 0) ≤
      (momentScalarAmp{year}Expected.1.1 : ℝ) + (momentScalarAmp{year}Expected.2 : ℝ) := by
    linarith
  have hgrowthUpper : Real.exp (2 * momentPhaseSlopeUpper2619 (momentBeta2620 : ℝ)
      {center_literal} {half_literal} * {half_literal}) ≤
      (momentScalarGrow{year}Expected.1.1 : ℝ) + (momentScalarGrow{year}Expected.2 : ℝ) := by
    linarith
  have hproduct := mul_le_mul hamplitudeUpper hgrowthUpper
    (le_of_lt (Real.exp_pos _))
    ((le_of_lt (Real.exp_pos _)).trans hamplitudeUpper)
  apply hbase.trans
  have hfactor : 0 ≤ (momentPanelResidualUpper{year} : ℝ) /
      (1 - (|{center_literal}| + {half_literal}) ^ 2) ^ 2 :=
    div_nonneg (Rat.cast_nonneg.mpr momentPanelResidualUpper_nonneg{year}) (sq_nonneg _)
  have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hproduct hfactor)
    (by positivity : 0 ≤ (2 : ℝ) * {half_literal} ^ 2)
  simpa only [momentPanelAnalyticCharge{year}, Rat.cast_mul, Rat.cast_add, Rat.cast_div,
    Rat.cast_sub{cast_neg}, Rat.cast_pow, Rat.cast_abs, Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_one] using h

theorem actualMomentPanel{tag}_integral_certificate2622 :
    |(storedWidth 0 ^ 2) *
      (∫ position in (-{half_literal})..{half_literal},
        realNormalizedMomentIntegrand2618 (storedWidth 0 ^ 2) (capturedNodes2584 0).re
          ({center_literal} + position)) - (momentPanelIntegralCenter{year} : ℝ)| ≤
      (momentPanelIntegralCharge{year} : ℝ) := by
  have hphase : (∫ position in (-{half_literal})..{half_literal},
      realNormalizedMomentIntegrand2618 (storedWidth 0 ^ 2) (capturedNodes2584 0).re
        ({center_literal} + position)) =
      (∫ position in (-{half_literal})..{half_literal},
        Real.exp (momentPhase2619 (momentBeta2620 : ℝ) {center_literal} position)) := by
    apply intervalIntegral.integral_congr
    intro position hposition
    rw [Set.uIcc_of_le (by norm_num :
      -({half_literal.removeprefix('(').removesuffix(')')} : ℝ) ≤
        {half_literal.removeprefix('(').removesuffix(')')})] at hposition
    rw [momentBeta_owner2620]
    exact realNormalizedMomentIntegrand2618_eq_phase2619 _ _ _ _
      (momentPanel_interior2619 {center_literal} {half_literal} position (by norm_num) hposition)
  rw [hphase, ← momentRadius_owner2620]
  have hcenter : (momentRadius2620 : ℝ) * (momentScalarAmp{year}Expected.1.1 : ℝ) *
      (momentPanelIntegral{year} : ℝ) = (momentPanelIntegralCenter{year} : ℝ) := by
    exact_mod_cast momentPanelCenter_replay{year}
  have hcharge : (momentRadius2620 : ℝ) * ((momentPanelAnalyticCharge{year} : ℝ) +
      (momentScalarAmp{year}Expected.2 : ℝ) * |(momentPanelIntegral{year} : ℝ)|) =
      (momentPanelIntegralCharge{year} : ℝ) := by
    exact_mod_cast momentPanelCharge_replay{year}
  have hamplitude := momentScalarAmp{year}_error
  rw [← momentBeta_owner2620] at hamplitude
  have hradius : 0 < (momentRadius2620 : ℝ) := by
    rw [momentRadius_owner2620]
    exact pow_pos (storedWidth_pos 0) 2
  rw [← hcenter, mul_assoc, ← mul_sub, abs_mul, abs_of_pos hradius]
  apply (mul_le_mul_of_nonneg_left
    ((abs_sub_le _ _ _).trans (add_le_add momentPanelPhase_error{year}
      (show |Real.exp (momentPhase2619 (momentBeta2620 : ℝ) {center_literal} 0) *
          (momentPanelIntegral{year} : ℝ) - (momentScalarAmp{year}Expected.1.1 : ℝ) *
            (momentPanelIntegral{year} : ℝ)| ≤
          (momentScalarAmp{year}Expected.2 : ℝ) * |(momentPanelIntegral{year} : ℝ)| from by
        rw [← sub_mul, abs_mul]
        exact mul_le_mul_of_nonneg_right hamplitude (abs_nonneg _)))) hradius.le).trans_eq hcharge

theorem actualMomentPanel{tag}_integral_error_le2622 :
    |(storedWidth 0 ^ 2) *
      (∫ position in ({lean_interval_literal(data['center'] - HALF_WIDTH)} : ℝ)..{lean_interval_literal(data['center'] + HALF_WIDTH)},
        realNormalizedMomentIntegrand2618 (storedWidth 0 ^ 2) (capturedNodes2584 0).re position) -
      (momentPanelIntegralCenter{year} : ℝ)| ≤ (1 : ℝ) / 10 ^ {data['charge_digits']} := by
  have h := actualMomentPanel{tag}_integral_certificate2622
  rw [intervalIntegral.integral_comp_add_left] at h
  norm_num only at h
  have hupper : (momentPanelIntegralCharge{year} : ℝ) ≤
      ((1 / 10 ^ {data['charge_digits']} : ℚ) : ℝ) :=
    Rat.cast_le.mpr momentPanelCharge_le{year}
  exact h.trans (by simpa using hupper)

end ConnesWeilRH.Dev
"""


def panel_sources(data):
    tag = f"{data['index']:03d}"
    return {f"C1RouteAMomentPanelScalars2622Panel{tag}.lean": scalar_sources(data),
            f"C1RouteAMomentPanelTable2622Panel{tag}.lean": table_sources(data),
            f"C1RouteAMomentActualPanel2622Panel{tag}.lean": consumer_sources(data)}


def audit_source(indices):
    imports = "\n".join(
        f"import ConnesWeilRH.Dev.C1RouteAMomentActualPanel2622Panel{index:03d}"
        for index in indices)
    prints = []
    for index in indices:
        year = f"2622P{index:03d}"
        for name in (f"momentPanelPhase_owner{year}", f"momentPanelGrowth_owner{year}",
                     f"momentScalarAmp{year}_replay", f"momentScalarAmp{year}_error",
                     f"momentScalarAmp{year}_radius_le",
                     f"momentScalarGrow{year}_replay", f"momentScalarGrow{year}_error",
                     f"momentScalarGrow{year}_radius_le",
                     f"momentPanelPrimitive_replay{year}", f"momentPanelResidual_replay{year}",
                     f"momentPanelResidualUpper_replay{year}", f"momentPanelIntegral_replay{year}",
                     f"momentPanelCenter_replay{year}", f"momentPanelCharge_replay{year}",
                     f"momentPanelCharge_le{year}", f"momentPanelResidualUpper_nonneg{year}",
                     f"momentPanelResidual_low_zero{year}", f"momentPanelResidual_tail_zero{year}",
                     f"momentPanelDenominator_eval{year}", f"momentPanelNumerator_eval{year}",
                     f"momentPanelResidual_eval{year}", f"momentPanelResidual_bound{year}",
                     f"momentPanelPolynomial_integral{year}", f"momentPanelPhase_error{year}",
                     f"actualMomentPanel{index:03d}_integral_certificate2622",
                     f"actualMomentPanel{index:03d}_integral_error_le2622"):
            prints.append(f"#print axioms ConnesWeilRH.Dev.{name}")
    return f"{imports}\n\n" + "\n".join(prints) + "\n"


def partition_pricing(owner):
    """Exact partition gate: the summed charges of ALL 180 panels must sit
    far inside the committed 2597 real rectangle width for entry (0,0)."""
    witness = json.loads(
        ROOT.joinpath("results/2351_moment_matrix_witness.json").read_text())
    entry = witness["matrix"][0][0]
    real_lower = Fraction(entry["real"]["lower_exact"])
    real_upper = Fraction(entry["real"]["upper_exact"])
    width = real_upper - real_lower
    charges = [panel_data(index, owner)["integral_charge"] for index in range(180)]
    total = sum(charges, Fraction(0))
    worst = max(range(180), key=lambda index: charges[index])
    if total * PARTITION_SAFETY > width:
        raise ValueError(
            f"partition charges {float(total):.6e} exceed the 2597 real width "
            f"{float(width):.6e} / {PARTITION_SAFETY}")
    return {"panel_count": 180, "sum_charge_exact": str(total),
            "worst_panel_index": worst,
            "worst_panel_charge_exact": str(charges[worst]),
            "target_real_width_exact": str(width),
            "safety_factor_required": PARTITION_SAFETY,
            "achieved_margin_exact": str(width / total)}


def payload_data(indices, panels, owner):
    return {"record": 2622, "entry": [0, 0], "panels": list(indices),
            "degree": DEGREE, "half_width_exact": str(HALF_WIDTH),
            "capture_sha256": owner["capture_sha256"],
            "witness_sha256": owner["witness_sha256"],
            "generator_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "scalar_generator_sha256": hashlib.sha256(
                ROOT.joinpath("scripts/generate_moment_scalar_certificate_2620.py").read_bytes()).hexdigest(),
            "panel_generator_sha256": hashlib.sha256(
                ROOT.joinpath("scripts/generate_moment_panel_certificate_2621.py").read_bytes()).hexdigest(),
            "partition_pricing": partition_pricing(owner),
            "panels_data": {str(index): {key: (",".join(str(value) for value in panel[key])
                                              if isinstance(panel[key], list) else str(panel[key]))
                                         for key in ("center", "phase", "growth",
                                                     "residual_upper", "integral",
                                                     "integral_center", "integral_charge",
                                                     "charge_digits")}
                            for index, panel in zip(indices, panels)},
            "lean_verified": False, "actual_entry_containment_lean_verified": False,
            "partition_assembly_lean_verified": False,
            "producer_go": False, "rh_claim": False}


def cross_check_panel94(panels):
    """Semantic regression: the 2622-shaped panel 094 must reproduce the
    committed record-2621 payload numbers exactly, entry by entry."""
    reference = json.loads(
        ROOT.joinpath("results/2621_moment_panel_payload.json").read_text())
    committed = reference["data"]
    panel = next(data for data in panels if data["index"] == 94)
    for key, value in (("residual_upper", panel["residual_upper"]),
                       ("integral", panel["integral"]),
                       ("integral_center", panel["integral_center"]),
                       ("integral_charge", panel["integral_charge"])):
        if str(value) != committed[key]:
            raise ValueError(f"panel094 regression drift on {key}: "
                             f"{value} != {committed[key]}")
    if panel["charge_digits"] != 82:
        raise ValueError("panel094 charge display digits drifted from the "
                         "committed 1/10^82 bound")
    for key, values in (("coefficients", panel["coefficients"]),
                        ("primitive", panel["primitive"]),
                        ("residual", panel["residual"])):
        if [str(value) for value in values] != committed[key]:
            raise ValueError(f"panel094 regression drift on {key}")


def generate(indices, write=True):
    owner = get_data()
    panels = [panel_data(index, owner) for index in indices]
    if 94 in indices:
        cross_check_panel94(panels)
    sources = {}
    for index, data in zip(indices, panels):
        sources.update(panel_sources(data))
    sources["C1RouteAMomentPanelBatchAudit2622.lean"] = audit_source(indices)
    payload = payload_data(indices, panels, owner)
    if not write:
        return sources, payload
    for filename, source in sources.items():
        (DEV / filename).write_text(source, encoding="utf-8", newline="\n")
    ROOT.joinpath("results/2622_moment_panel_batch_payload.json").write_text(
        json.dumps(payload, indent=2) + "\n", encoding="utf-8", newline="\n")
    for index, data in zip(indices, panels):
        print(f"panel {index:03d}: residual upper ~{float(data['residual_upper']):.6e}, "
              f"integral charge ~{float(data['integral_charge']):.6e}", flush=True)
    return sources, payload


def main():
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--panels", default="90,91,92,93,94,95,96,97,98,99",
                        help="comma-separated panel indices in [0, 179]; "
                             "94 doubles as the semantic regression control")
    arguments = parser.parse_args()
    indices = [int(value) for value in arguments.panels.split(",")]
    generate(indices)


if __name__ == "__main__":
    main()
