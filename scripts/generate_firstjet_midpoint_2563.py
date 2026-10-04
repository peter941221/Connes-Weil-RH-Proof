"""Generate the order-1 signed jet certificate at the cell2700 midpoint.

Clones the accepted 2547 per-family replay and the 2543 rounding/aggregate
templates at order 1, against the shared cell2700 midpoint position from the
2548 boundary module. Feeds the 2562 correction-second decomposition, which
needs signedJetUpper2539 1 at the cell midpoint; every other ingredient of
that decomposition is already certified (2549/2551/2556).
"""
from fractions import Fraction as Q
from math import isqrt
import json
import textwrap

from generate_complex_exp_node_2541 import ROOT, CAPTURE, real, pair as complex_pair, rounded, up, mul, add
from generate_compact_replay_2542 import pair
from price_boundary_precision_2547 import precision_evaluate
from routea_exp_schedule_probe_2542 import R, STEP
from routea_derivative_pricing_2543 import multiplier

ORDER = 1
SIGMA = Q(1, 2)
GRID_INDEX = Q(5401, 2)
LEAN_SIGMA = "(1/2)"


def wrap(source):
    lines = []
    for line in source.splitlines():
        indent = len(line) - len(line.lstrip())
        lines.extend(textwrap.wrap(line, width=98, subsequent_indent=" " * (indent + 4),
                                   break_long_words=False, break_on_hyphens=False) or [""])
    return "\n".join(lines) + "\n"


def build_parts():
    x = -R + GRID_INDEX * STEP
    raw = json.loads(CAPTURE.read_text())["owner_capture"]["families_hex"]
    rows = json.loads((ROOT / "results/2338_exact_interpolation_repair.json").read_text())["coefficient_rows"]

    parts = [f"""import ConnesWeilRH.Dev.C1RouteACompactExp1602547
import ConnesWeilRH.Dev.C1RouteADerivativeMultiplier2543
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541
import ConnesWeilRH.Dev.C1RouteABoundaryMidpoint2548

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

theorem firstJetMidpoint_triangle2563 (a b c : ℂ) : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
  calc
    ‖a - c‖ = ‖(a - b) + (b - c)‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _

theorem fjmidZero2563 : embedPair2542 (0, 0) = 0 := by
  apply Complex.ext <;> norm_num [embedPair2542]

"""]

    rounded_rows = []
    total = (Q(0), Q(0))
    charge = Q(0)
    active = []
    for i, (values, row) in enumerate(zip(raw, rows)):
        width, theta = (Q.from_float(float.fromhex(v)) for v in values)
        radius = width ** 2
        p = f"fjmidP{i:03d}"
        if abs(x) < radius:
            active.append(i)
            factor = multiplier(ORDER, radius, theta, SIGMA, x)
            center, error, depth = precision_evaluate(radius, theta, x, SIGMA, 160)
            z = ((SIGMA * x - 30 / (1 - (x / radius) ** 2)) / 2 ** depth,
                 theta * x / 2 ** depth)
            out = rounded(mul(factor, center))
            fam_radius = up(sum(abs(v) for v in factor) * error + Q(1, 2 ** 99))
            assert sum(abs(v) for v in out) + fam_radius <= 1, (i, float(out[0]), float(fam_radius))
            parts.append(f"""noncomputable def {p}Input2563 : RatPair2542 := {pair(z)}

def {p}Center2563 : RatPair2542 := {pair(center)}

def {p}Factor2563 : RatPair2542 := {pair(factor)}

noncomputable def {p}Error2563 : ℝ := {real(error)}

theorem {p}BaseError2563 :
    ‖weightedUnitJet2539 0 {LEAN_SIGMA} nodeModulation2541 ⟨{i}, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 {p}Center2563‖ ≤ {p}Error2563 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨{i}, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 {p}Input2563‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, {p}Input2563]
  have hc : (compactExp2547 {p}Input2563 {depth}).1 = {p}Center2563 := by cbv
  have he : ((compactExp2547 {p}Input2563 {depth}).2 : ℝ) = {p}Error2563 := by
    have hq : (compactExp2547 {p}Input2563 {depth}).2 =
        {real(error).replace('ℝ', 'ℚ')} := by cbv
    rw [hq]
    norm_num [{p}Error2563]
  have h := compactExp_error2547 {p}Input2563 hz {depth}
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 {LEAN_SIGMA} nodeModulation2541 ⟨{i}, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^{depth} * embedPair2542 {p}Input2563) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, {p}Input2563, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem {p}DerivativeError2563 :
    ‖weightedUnitJet2539 {ORDER} {LEAN_SIGMA} nodeModulation2541 ⟨{i}, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 {p}Factor2563 * embedPair2542 {p}Center2563‖ ≤
        (pairMagnitude2542 {p}Factor2563 : ℝ) * {p}Error2563 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨{i}, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 {ORDER} {LEAN_SIGMA}
      (nodeModulation2541 ⟨{i}, by omega⟩)
      (storedWidth ⟨{i}, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 {p}Factor2563 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      {p}Factor2563, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 {ORDER} (by omega) {LEAN_SIGMA}
    (nodeModulation2541 ⟨{i}, by omega⟩) (pow_pos (storedWidth_pos ⟨{i}, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv {ORDER} _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ {p}BaseError2563
    (embedPair_magnitude2542 {p}Factor2563)

def {p}Rounded2563 : RatPair2542 :=
  {pair(out)}

noncomputable def {p}Radius2563 : ℝ := {real(fam_radius)}

theorem {p}RoundCompute2563 :
    pairRound2542 (pairMul2542 {p}Factor2563 {p}Center2563) = {p}Rounded2563 := by
  cbv

theorem {p}RoundedError2563 :
    ‖weightedUnitJet2539 {ORDER} {LEAN_SIGMA} nodeModulation2541 ⟨{i}, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 {p}Rounded2563‖ ≤ {p}Radius2563 := by
  have hr := embedPair_round_error2542 (pairMul2542 {p}Factor2563 {p}Center2563)
  rw [{p}RoundCompute2563, embedPair_mul2542] at hr
  have h := (firstJetMidpoint_triangle2563
    (weightedUnitJet2539 {ORDER} {LEAN_SIGMA} nodeModulation2541 ⟨{i}, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 {p}Factor2563 * embedPair2542 {p}Center2563)
    (embedPair2542 {p}Rounded2563)).trans (add_le_add {p}DerivativeError2563 hr)
  apply h.trans
  norm_num [pairMagnitude2542, {p}Factor2563, {p}Error2563, rounding2542, {p}Radius2563]

theorem {p}DerivativeNorm2563 :
    ‖weightedUnitJet2539 {ORDER} {LEAN_SIGMA} nodeModulation2541 ⟨{i}, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetMidpoint_triangle2563
    (weightedUnitJet2539 {ORDER} {LEAN_SIGMA} nodeModulation2541 ⟨{i}, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 {p}Rounded2563) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add {p}RoundedError2563 (embedPair_magnitude2542 {p}Rounded2563))
  apply h'.trans
  norm_num [{p}Radius2563, pairMagnitude2542, {p}Rounded2563]

""")
        else:
            out = (Q(0), Q(0))
            fam_radius = Q(0)
            parts.append(f"""def {p}Center2563 : RatPair2542 := (0, 0)

def {p}Factor2563 : RatPair2542 := (0, 0)

noncomputable def {p}Error2563 : ℝ := 0

theorem {p}Exterior2563 (n : ℕ) :
    weightedUnitJet2539 n {LEAN_SIGMA} nodeModulation2541 ⟨{i}, by omega⟩
      edgeMidpointPosition2548 = 0 := by
  have hx : storedWidth ⟨{i}, by omega⟩ ^ 2 ≤ |edgeMidpointPosition2548| := by
    norm_num [storedWidth, edgeMidpointPosition2548]
  exact weightedFamily_outside_zero2543 n {LEAN_SIGMA}
    (nodeModulation2541 ⟨{i}, by omega⟩)
    (pow_pos (storedWidth_pos ⟨{i}, by omega⟩) 2) hx

theorem {p}BaseError2563 :
    ‖weightedUnitJet2539 0 {LEAN_SIGMA} nodeModulation2541 ⟨{i}, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 {p}Center2563‖ ≤ {p}Error2563 := by
  rw [{p}Exterior2563]
  norm_num [{p}Center2563, {p}Error2563, fjmidZero2563]

theorem {p}DerivativeError2563 :
    ‖weightedUnitJet2539 {ORDER} {LEAN_SIGMA} nodeModulation2541 ⟨{i}, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 {p}Factor2563 * embedPair2542 {p}Center2563‖ ≤
        (pairMagnitude2542 {p}Factor2563 : ℝ) * {p}Error2563 := by
  rw [{p}Exterior2563]
  norm_num [{p}Factor2563, {p}Center2563, {p}Error2563, pairMagnitude2542, fjmidZero2563]

def {p}Rounded2563 : RatPair2542 := (0, 0)

noncomputable def {p}Radius2563 : ℝ := 0

theorem {p}RoundCompute2563 :
    pairRound2542 (pairMul2542 {p}Factor2563 {p}Center2563) = {p}Rounded2563 := by
  cbv

theorem {p}RoundedError2563 :
    ‖weightedUnitJet2539 {ORDER} {LEAN_SIGMA} nodeModulation2541 ⟨{i}, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 {p}Rounded2563‖ ≤ {p}Radius2563 := by
  rw [{p}Exterior2563]
  norm_num [{p}Rounded2563, {p}Radius2563, fjmidZero2563]

theorem {p}DerivativeNorm2563 :
    ‖weightedUnitJet2539 {ORDER} {LEAN_SIGMA} nodeModulation2541 ⟨{i}, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  rw [{p}Exterior2563]
  norm_num

""")
        coeff = tuple(
            (Q(row["ideal_base_coefficient"][part]["lower_exact"]) +
             Q(row["ideal_base_coefficient"][part]["upper_exact"])) / 2
            for part in ("real", "imag"))
        if abs(x) < radius:
            total = add(total, mul(coeff, out))
            charge += sum(abs(v) for v in coeff) * fam_radius
        rounded_rows.append((out, fam_radius))

    for name, typ, entry in (("fjmidValue2563", "ℂ", lambda i: f"embedPair2542 fjmidP{i:03d}Rounded2563"),
                             ("fjmidError2563", "ℝ", lambda i: f"fjmidP{i:03d}Radius2563")):
        parts.append(f"noncomputable def {name} (i : Fin 30) : {typ} :=\n  match i.val with\n")
        parts.extend(f"  | {i} => {entry(i)}\n" for i in range(30))
        parts.append("  | _ => 0\n\n")

    for name, goal, suffix in (
            ("fjmidExpError2563", "‖weightedUnitJet2539 1 (1/2) nodeModulation2541 i edgeMidpointPosition2548 - fjmidValue2563 i‖ ≤ fjmidError2563 i", "RoundedError"),
            ("fjmidUnitNorm2563", "‖weightedUnitJet2539 1 (1/2) nodeModulation2541 i edgeMidpointPosition2548‖ ≤ 1", "DerivativeNorm")):
        parts.append(f"theorem {name} (i : Fin 30) :\n    {goal} := by\n  fin_cases i\n")
        parts.extend(f"  · simpa only [fjmidValue2563, fjmidError2563] using fjmidP{i:03d}{suffix}2563\n"
                     for i in range(30))
        parts.append("\n")

    square = sum(v * v for v in total)
    scale = 10 ** 8
    norm_upper = Q(isqrt(square.numerator * scale ** 2 // square.denominator) + 1, scale)
    upper = norm_upper + Q(1, 10 ** 7)
    assert norm_upper ** 2 >= square and charge <= Q(1, 10 ** 8)
    parts.append(f"noncomputable def fjmidSum2563 : ℂ := {complex_pair(total)}\n\n")
    parts.append(f"noncomputable def fjmidUpper2563 : ℝ := {real(upper)}\n\n")
    cdefs = ",\n      ".join(f"fjmidP{i:03d}Rounded2563" for i in range(30))
    edefs = ",\n      ".join(f"fjmidP{i:03d}Radius2563" for i in range(30))
    parts.append(f"""theorem fjmidSum_eq2563 :
    (∑ i : Fin 30, baseCoefficientCenter2540 i * fjmidValue2563 i) =
      fjmidSum2563 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, fjmidValue2563,
      fjmidSum2563, embedPair2542, {cdefs}, Complex.mul_re, Complex.mul_im]

theorem fjmidSum_norm2563 :
    ‖∑ i : Fin 30, baseCoefficientCenter2540 i * fjmidValue2563 i‖ ≤ {real(norm_upper)} := by
  rw [fjmidSum_eq2563]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [fjmidSum2563]

theorem fjmidCharge2563 :
    (∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
      |(baseCoefficientCenter2540 i).im|) * fjmidError2563 i) ≤ (1 : ℝ)/10^8 := by
  rw [sum30_chain2541]
  norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, fjmidError2563, {edefs}]

""")

    old = (ROOT / "ConnesWeilRH/Dev/C1RouteANonzeroNode2541.lean").read_text()
    body = old[old.index("theorem signedJet_nonzero_le2541"):old.index("theorem production_grid_nonzero2541")]
    replacements = {"signedJet_nonzero_le2541": "firstJetMidpointUpper_le2563",
                    "weightedPhysical_nonzero_le2541": "weightedPhysicalFirstJetMidpoint_le2563",
                    "nodeExp_error2541": "fjmidExpError2563",
                    "nodeUnit_norm2541": "fjmidUnitNorm2563",
                    "nodeSum_norm2541": "fjmidSum_norm2563",
                    "nodeEvaluation_charge2541": "fjmidCharge2563",
                    "nodePosition2541": "edgeMidpointPosition2548",
                    "nodeValue2541": "fjmidValue2563",
                    "nodeError2541": "fjmidError2563",
                    "nodeUpper2541": "fjmidUpper2563"}
    for a, b in replacements.items():
        body = body.replace(a, b)
    body = body.replace("signedJetUpper2539 0", "signedJetUpper2539 1")
    body = body.replace("weightedUnitJet2539 0", "weightedUnitJet2539 1")
    body = body.replace("weightedPhysical2539_jet_le_center_error 0",
                        "weightedPhysical2539_jet_le_center_error 1")
    body = body.replace(
        "‖weightedPhysical2539 (1/2) coefficients nodeModulation2541 edgeMidpointPosition2548‖",
        "‖iteratedDeriv 1 (weightedPhysical2539 (1/2) coefficients nodeModulation2541) edgeMidpointPosition2548‖")
    body = body.replace("simpa only [iteratedDeriv_zero] using h.trans", "exact h.trans")
    parts.extend([body, "end ConnesWeilRH.Dev\n\n"])

    parts.append("#print axioms ConnesWeilRH.Dev.fjmidExpError2563\n")
    parts.append("#print axioms ConnesWeilRH.Dev.fjmidSum_eq2563\n")
    parts.append("#print axioms ConnesWeilRH.Dev.fjmidSum_norm2563\n")
    parts.append("#print axioms ConnesWeilRH.Dev.fjmidCharge2563\n")
    parts.append("#print axioms ConnesWeilRH.Dev.firstJetMidpointUpper_le2563\n")
    parts.append("#print axioms ConnesWeilRH.Dev.weightedPhysicalFirstJetMidpoint_le2563\n")

    return dict(output=wrap("".join(parts)), active=len(active), upper=upper, charge=charge)


def render():
    return build_parts()["output"]


def main():
    state = build_parts()
    output: str = str(state["output"])
    target = ROOT / "ConnesWeilRH/Dev/C1RouteAFirstJetMidpoint2563.lean"
    target.write_text(output, encoding="utf-8", newline="\n")
    print("FIRST_JET_MIDPOINT_2563_GENERATED active", state["active"], "families",
          "upper", str(state["upper"]), float(state["upper"]), "charge", float(state["charge"]),
          flush=True)


if __name__ == "__main__":
    main()
