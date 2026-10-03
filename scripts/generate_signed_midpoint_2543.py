"""Round derivative centers and certify the actual signed midpoint sum."""
from fractions import Fraction as Q
import json
from math import isqrt
import textwrap

from generate_complex_exp_node_2541 import ROOT, real, pair as complex_pair, rounded, up, mul, add
from generate_compact_replay_2542 import pair
from validate_compact_replay_2542 import value
from validate_adaptive_nodes_2542 import scalar_def


def render():
    source = (ROOT/"ConnesWeilRH/Dev/C1RouteAMidpointDerivatives2543.lean").read_text()
    coefficients = json.loads((ROOT/"results/2338_exact_interpolation_repair.json").read_text())["coefficient_rows"]
    parts = ["""import ConnesWeilRH.Dev.C1RouteAMidpointDerivatives2543

namespace ConnesWeilRH.Dev

open scoped BigOperators

theorem midpoint_triangle2543 (a b c : ℂ) : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
  calc
    ‖a - c‖ = ‖(a - b) + (b - c)‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _

"""]
    rows, total, charge = [], (Q(0),Q(0)), Q(0)
    for i in range(30):
        p = f"midpointP{i:03d}"
        factor = value(source,p+"Factor2543")
        center = value(source,p+"Center2543")
        error = scalar_def(source,p+"Error2543")
        out = rounded(mul(factor,center))
        radius = up(sum(abs(v) for v in factor)*error+Q(1,2**99))
        assert sum(abs(v) for v in out)+radius <= 1
        rows.append((out,radius))
        coeff = tuple((Q(coefficients[i]["ideal_base_coefficient"][part]["lower_exact"])+
                       Q(coefficients[i]["ideal_base_coefficient"][part]["upper_exact"]))/2
                      for part in ("real","imag"))
        total = add(total,mul(coeff,out))
        charge += sum(abs(v) for v in coeff)*radius
        parts.append(f"""def {p}Rounded2543 : RatPair2542 :=
  {pair(out)}

noncomputable def {p}Radius2543 : ℝ := {real(radius)}

theorem {p}RoundCompute2543 :
    pairRound2542 (pairMul2542 {p}Factor2543 {p}Center2543) = {p}Rounded2543 := by
  cbv

theorem {p}RoundedError2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨{i}, by omega⟩ midpointPosition2543 -
      embedPair2542 {p}Rounded2543‖ ≤ {p}Radius2543 := by
  have hr := embedPair_round_error2542 (pairMul2542 {p}Factor2543 {p}Center2543)
  rw [{p}RoundCompute2543, embedPair_mul2542] at hr
  have h := (midpoint_triangle2543
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨{i}, by omega⟩ midpointPosition2543)
    (embedPair2542 {p}Factor2543 * embedPair2542 {p}Center2543)
    (embedPair2542 {p}Rounded2543)).trans (add_le_add {p}DerivativeError2543 hr)
  apply h.trans
  norm_num [pairMagnitude2542, {p}Factor2543, {p}Error2543, rounding2542, {p}Radius2543]

theorem {p}DerivativeNorm2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨{i}, by omega⟩ midpointPosition2543‖ ≤ 1 := by
  have h := midpoint_triangle2543
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨{i}, by omega⟩ midpointPosition2543)
    (embedPair2542 {p}Rounded2543) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add {p}RoundedError2543 (embedPair_magnitude2542 {p}Rounded2543))
  apply h'.trans
  norm_num [{p}Radius2543, pairMagnitude2542, {p}Rounded2543]

""")
    for name,typ,entry in (("signedMidpointValue2543","ℂ",lambda i:f"embedPair2542 midpointP{i:03d}Rounded2543"),
                           ("signedMidpointError2543","ℝ",lambda i:f"midpointP{i:03d}Radius2543")):
        parts.append(f"noncomputable def {name} (i : Fin 30) : {typ} :=\n  match i.val with\n")
        parts.extend(f"  | {i} => {entry(i)}\n" for i in range(30))
        parts.append("  | _ => 0\n\n")
    for name,goal,suffix in (
        ("signedMidpointExpError2543", "‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i midpointPosition2543 - signedMidpointValue2543 i‖ ≤ signedMidpointError2543 i", "RoundedError"),
        ("signedMidpointUnitNorm2543", "‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i midpointPosition2543‖ ≤ 1", "DerivativeNorm")):
        parts.append(f"theorem {name} (i : Fin 30) :\n    {goal} := by\n  fin_cases i\n")
        parts.extend(f"  · simpa only [signedMidpointValue2543, signedMidpointError2543] using midpointP{i:03d}{suffix}2543\n" for i in range(30))
        parts.append("\n")
    square = sum(v*v for v in total)
    scale = 10**8
    norm_upper = Q(isqrt(square.numerator*scale**2//square.denominator)+1,scale)
    upper = norm_upper+Q(1,10**7)
    assert norm_upper**2 >= square and charge <= Q(1,10**8)
    parts.append(f"noncomputable def signedMidpointSum2543 : ℂ := {complex_pair(total)}\n\n")
    parts.append(f"noncomputable def signedMidpointUpper2543 : ℝ := {real(upper)}\n\n")
    cdefs = ",\n      ".join(f"midpointP{i:03d}Rounded2543" for i in range(30))
    edefs = ",\n      ".join(f"midpointP{i:03d}Radius2543" for i in range(30))
    parts.append(f"""theorem signedMidpointSum_eq2543 :
    (∑ i : Fin 30, baseCoefficientCenter2540 i * signedMidpointValue2543 i) =
      signedMidpointSum2543 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, signedMidpointValue2543,
      signedMidpointSum2543, embedPair2542, {cdefs}, Complex.mul_re, Complex.mul_im]

theorem signedMidpointSum_norm2543 :
    ‖∑ i : Fin 30, baseCoefficientCenter2540 i * signedMidpointValue2543 i‖ ≤ {real(norm_upper)} := by
  rw [signedMidpointSum_eq2543]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [signedMidpointSum2543]

theorem signedMidpointCharge2543 :
    (∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
      |(baseCoefficientCenter2540 i).im|) * signedMidpointError2543 i) ≤ (1 : ℝ)/10^8 := by
  rw [sum30_chain2541]
  norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, signedMidpointError2543, {edefs}]

""")
    old = (ROOT/"ConnesWeilRH/Dev/C1RouteANonzeroNode2541.lean").read_text()
    body = old[old.index("theorem signedJet_nonzero_le2541"):old.index("theorem production_grid_nonzero2541")]
    replacements = {"signedJet_nonzero_le2541":"signedMidpointUpper_le2543",
                    "weightedPhysical_nonzero_le2541":"weightedPhysical_second_midpoint_le2543",
                    "nodeExp_error2541":"signedMidpointExpError2543",
                    "nodeUnit_norm2541":"signedMidpointUnitNorm2543",
                    "nodeSum_norm2541":"signedMidpointSum_norm2543",
                    "nodeEvaluation_charge2541":"signedMidpointCharge2543",
                    "nodePosition2541":"midpointPosition2543", "nodeValue2541":"signedMidpointValue2543",
                    "nodeError2541":"signedMidpointError2543", "nodeUpper2541":"signedMidpointUpper2543"}
    for a,b in replacements.items():
        body = body.replace(a,b)
    body = body.replace("signedJetUpper2539 0", "signedJetUpper2539 2")
    body = body.replace("weightedUnitJet2539 0", "weightedUnitJet2539 2")
    body = body.replace("weightedPhysical2539_jet_le_center_error 0", "weightedPhysical2539_jet_le_center_error 2")
    body = body.replace("‖weightedPhysical2539 (1/2) coefficients nodeModulation2541 midpointPosition2543‖",
                        "‖iteratedDeriv 2 (weightedPhysical2539 (1/2) coefficients nodeModulation2541) midpointPosition2543‖")
    body = body.replace("simpa only [iteratedDeriv_zero] using h.trans", "exact h.trans")
    parts.extend([body,"end ConnesWeilRH.Dev\n\n"])
    for name in ("signedMidpointExpError2543","signedMidpointSum_eq2543","signedMidpointCharge2543",
                 "signedMidpointUpper_le2543","weightedPhysical_second_midpoint_le2543"):
        parts.append(f"#print axioms ConnesWeilRH.Dev.{name}\n")
    lines = []
    for line in "".join(parts).splitlines():
        indent = len(line)-len(line.lstrip())
        lines.extend(textwrap.wrap(line,width=98,subsequent_indent=" "*(indent+4),
                                   break_long_words=False,break_on_hyphens=False) or [""])
    return "\n".join(lines)+"\n",upper,charge


if __name__ == "__main__":
    source,upper,charge = render()
    (ROOT/"ConnesWeilRH/Dev/C1RouteASignedMidpoint2543.lean").write_text(source,encoding="utf-8",newline="\n")
    print("SIGNED_MIDPOINT_GENERATED",str(upper),float(upper),"charge",float(charge),flush=True)
