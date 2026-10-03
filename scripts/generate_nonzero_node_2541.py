"""Assemble all 30 complex-exponential witnesses at production node 5121."""
import argparse
from fractions import Fraction as Q
import json
from math import isqrt

from generate_complex_exp_node_2541 import ROOT, CAPTURE, NODE, witness, real, pair, add, mul

TARGET = ROOT / "ConnesWeilRH/Dev/C1RouteANonzeroNode2541.lean"


def render():
    rows = json.loads((ROOT/"results/2338_exact_interpolation_repair.json").read_text())["coefficient_rows"]
    capture = json.loads(CAPTURE.read_text())["owner_capture"]["families_hex"]
    witnesses = [witness(i) for i in range(30)]
    total = (Q(0), Q(0))
    for row, (_, _, squares, _, _) in zip(rows, witnesses):
        center = tuple((Q(row["ideal_base_coefficient"][part]["lower_exact"])+
                        Q(row["ideal_base_coefficient"][part]["upper_exact"]))/2
                       for part in ("real", "imag"))
        total = add(total, mul(center, squares[-1]))
    norm_square = total[0]**2+total[1]**2
    scaled = norm_square*10**16
    norm_upper = Q(isqrt(scaled.numerator//scaled.denominator)+1, 10**8)
    assert norm_square <= norm_upper**2
    final_upper = norm_upper+Q(1,10**10)
    zdefs = ", ".join(f"nodeZP{i:03d}2541" for i in range(30))
    sdefs = ", ".join(f"nodeSP{i:03d}2541" for i in range(30))
    edefs = ", ".join(f"nodeEP{i:03d}2541" for i in range(30))

    def normdefs(names, indent="    "):
        # Keep generated proof source readable without changing its arithmetic.
        return (",\n"+indent).join(names.split(", "))

    lines = [f"import ConnesWeilRH.Dev.C1RouteAExpNode2541P{i:03d}" for i in range(30)]
    lines += ["import ConnesWeilRH.Dev.C1RouteACenterNode2540", "",
              "/-! Signed nonzero node certificate; exact interpolation membership remains open. -/",
              "", "namespace ConnesWeilRH.Dev", "", "open scoped BigOperators",
              "open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit",
              "open ConnesWeilRH.Source.C1RouteAItem5Arithmetic", "",
              f"noncomputable def nodePosition2541 : ℝ := {real(NODE)}", "",
              f"noncomputable def nodeSumValue2541 : ℂ := {pair(total)}", "",
              f"noncomputable def nodeUpper2541 : ℝ := {real(final_upper)}", ""]
    for name, typ, values in (
        ("nodeZ2541", "ℂ", [f"nodeZP{i:03d}2541" for i in range(30)]),
        ("nodeValue2541", "ℂ", [f"nodeSP{i:03d}2541 6" for i in range(30)]),
        ("nodeError2541", "ℝ", [f"nodeEP{i:03d}2541 6" for i in range(30)]),
        ("nodeModulation2541", "ℝ", [real(Q.from_float(float.fromhex(t[1]))) for t in capture]),
    ):
        lines += [f"noncomputable def {name} (i : Fin 30) : {typ} :=", "  match i.val with"]
        lines += [f"  | {i} => {value}" for i,value in enumerate(values)]
        lines += ["  | _ => 0", ""]
    lines += [
        "theorem nodeUnit_eq2541 (i : Fin 30) :",
        "    weightedUnitJet2539 0 (1/2) nodeModulation2541 i nodePosition2541 =",
        "      Complex.exp ((2 : ℂ)^6 * nodeZ2541 i) := by",
        "  have hx : |nodePosition2541| < storedWidth i ^ 2 := by",
        "    fin_cases i <;> norm_num [nodePosition2541, storedWidth]",
        "  simp only [weightedUnitJet2539, iteratedDeriv_zero]",
        "  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]",
        "  congr 1",
        "  fin_cases i <;> apply Complex.ext <;>",
        "    norm_num [nodePosition2541, nodeModulation2541, storedWidth, nodeZ2541,",
        "      " + normdefs(zdefs, "      ") + ", Complex.mul_re, Complex.mul_im]", "",
        "theorem nodeExp_error2541 (i : Fin 30) :",
        "    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 i nodePosition2541 -",
        "      nodeValue2541 i‖ ≤ nodeError2541 i := by",
        "  rw [nodeUnit_eq2541]",
        "  fin_cases i"]
    lines += [f"  · exact nodeExpP{i:03d}_error2541" for i in range(30)]
    lines += ["", "theorem nodeUnit_norm2541 (i : Fin 30) :",
        "    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 i nodePosition2541‖ ≤ 1 := by",
        "  rw [nodeUnit_eq2541, Complex.norm_exp, Real.exp_le_one_iff]",
        "  fin_cases i <;> norm_num [nodeZ2541,",
        "    " + normdefs(zdefs) + ", Complex.mul_re, Complex.mul_im]", "",
        "theorem nodeSum_eq2541 :",
        "    (∑ i : Fin 30, baseCoefficientCenter2540 i * nodeValue2541 i) =",
        "      nodeSumValue2541 := by",
        "  rw [sum30_chain2541]",
        "  apply Complex.ext <;>",
        "    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, nodeValue2541,",
        "      nodeSumValue2541, " + normdefs(sdefs, "      ") + ", Complex.mul_re, Complex.mul_im]", "",
        "theorem nodeSum_norm2541 :",
        "    ‖∑ i : Fin 30, baseCoefficientCenter2540 i * nodeValue2541 i‖ ≤",
        f"      {real(norm_upper)} := by",
        "  rw [nodeSum_eq2541]",
        "  apply complex_norm_le_of_sq2541 _ _ (by norm_num)",
        "  norm_num [nodeSumValue2541]", "",
        "theorem nodeEvaluation_charge2541 :",
        "    (∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +",
        "      |(baseCoefficientCenter2540 i).im|) * nodeError2541 i) ≤ (1 : ℝ)/10^12 := by",
        "  rw [sum30_chain2541]",
        "  norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, nodeError2541,",
        "    " + normdefs(edefs) + "]", "",
        "theorem signedJet_nonzero_le2541 :",
        "    signedJetUpper2539 0 (1/2) baseCoefficientCenter2540 baseCoefficientError2540",
        "      nodeModulation2541 nodePosition2541 ≤ nodeUpper2541 := by",
        "  have hsum :",
        "      ‖∑ i : Fin 30, baseCoefficientCenter2540 i *",
        "        weightedUnitJet2539 0 (1/2) nodeModulation2541 i nodePosition2541‖ ≤",
        "      ‖∑ i : Fin 30, baseCoefficientCenter2540 i * nodeValue2541 i‖ +",
        "        ∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +",
        "          |(baseCoefficientCenter2540 i).im|) * nodeError2541 i := by",
        "    apply norm_sum_le_center_sum_add_error2531",
        "    intro i _",
        "    rw [← mul_sub, norm_mul]",
        "    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _) (nodeExp_error2541 i)",
        "      (norm_nonneg _) (by positivity)",
        "  have heach : ∀ i : Fin 30, baseCoefficientError2540 i *",
        "      ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 i nodePosition2541‖ ≤",
        "        (1 : ℝ)/10^30 := by",
        "    intro i",
        "    have h := mul_le_mul_of_nonneg_left (nodeUnit_norm2541 i)",
        "      (by norm_num [baseCoefficientError2540] : 0 ≤ baseCoefficientError2540 i)",
        "    simpa [baseCoefficientError2540] using h",
        "  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)",
        "  have he' : (∑ i : Fin 30, baseCoefficientError2540 i *",
        "      ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 i nodePosition2541‖) ≤",
        "        (30 : ℝ)/10^30 := by simpa using he",
        "  unfold signedJetUpper2539 nodeUpper2541",
        "  linarith [nodeSum_norm2541, nodeEvaluation_charge2541]", "",
        "theorem weightedPhysical_nonzero_le2541 (coefficients : Fin 30 → ℂ)",
        "    (hbox : ∀ i, (baseCoefficientBox2540 i).Mem (coefficients i)) :",
        "    ‖weightedPhysical2539 (1/2) coefficients nodeModulation2541 nodePosition2541‖ ≤",
        "      nodeUpper2541 := by",
        "  have h := weightedPhysical2539_jet_le_center_error 0 (1/2) coefficients",
        "    baseCoefficientCenter2540 baseCoefficientError2540 nodeModulation2541",
        "    (fun i => baseCoefficient_error_of_box2540 i (coefficients i) (hbox i)) nodePosition2541",
        "  simpa only [iteratedDeriv_zero] using h.trans signedJet_nonzero_le2541", "",
        "theorem production_grid_nonzero2541 :",
        "    -stripRadius2303 + (5121 : ℝ)*(2*stripRadius2303/10240) = nodePosition2541 := by",
        "  norm_num [stripRadius2303, nodePosition2541]", "",
        "end ConnesWeilRH.Dev", ""]
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    expected = render()
    if args.check:
        assert TARGET.read_text(encoding="utf-8") == expected
        print("NONZERO_NODE_ASSEMBLY_REGEN_PASS")
    else:
        TARGET.write_text(expected, encoding="utf-8", newline="\n")
        print("Generated", TARGET.name)


if __name__ == "__main__":
    main()
