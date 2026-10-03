"""Generate same-owner adaptive certificates at named production nodes."""
import argparse
from fractions import Fraction as Q
import json
from math import isqrt
import textwrap

from generate_complex_exp_node_2541 import ROOT, CAPTURE, real, pair as complex_pair, add, mul
from generate_compact_replay_2542 import pair, rational
from routea_exp_schedule_probe_2542 import evaluate, R, STEP


def render(index, sign):
    tag = f"N{index:05d}{'Plus' if sign > 0 else 'Minus'}"
    prefix = f"adaptive{tag}"
    x, sigma = -R + index*STEP, Q(sign, 2)
    families = json.loads(CAPTURE.read_text())["owner_capture"]["families_hex"]
    coefficients = json.loads((ROOT / "results/2338_exact_interpolation_repair.json").read_text())["coefficient_rows"]
    rows, centers = [], []
    for raw, row in zip(families, coefficients):
        width, theta = (Q.from_float(float.fromhex(v)) for v in raw)
        rows.append(evaluate(width**2, theta, x, sigma))
        centers.append(tuple((Q(row["ideal_base_coefficient"][p]["lower_exact"])+
                              Q(row["ideal_base_coefficient"][p]["upper_exact"]))/2
                             for p in ("real", "imag")))
    text = ["""import ConnesWeilRH.Dev.C1RouteACompactExp2542
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

""", f"noncomputable def {prefix}Position2542 : ℝ := {real(x)}\n\n"]
    pos = f"{prefix}Position2542"
    for i, row in enumerate(rows):
        p = f"{prefix}P{i:03d}"
        out = p + "Output2542"
        text.append(f"def {out} : RatState2542 :=\n  ({pair(row['center'])},\n    {rational(row['error'])})\n\n")
        unit = f"weightedUnitJet2539 0 ({real(sigma)}) nodeModulation2541 ⟨{i}, by omega⟩ {pos}"
        if row["exterior"]:
            text.append(f"""theorem {p}Zero2542 : {unit} = 0 := by
  have hx : ¬ |{pos}| < storedWidth ⟨{i}, by omega⟩ ^ 2 := by
    norm_num [{pos}, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero, weightedFunction2348,
    externalFamilyValue2344, if_neg hx, mul_zero]

theorem {p}Error2542 :
    ‖{unit} - embedPair2542 {out}.1‖ ≤ ({out}.2 : ℝ) := by
  have hz : embedPair2542 {out}.1 = 0 := by
    apply Complex.ext <;> norm_num [{out}, embedPair2542]
  rw [{p}Zero2542, hz]
  norm_num [{out}]

theorem {p}Norm2542 : ‖{unit}‖ ≤ 1 := by
  rw [{p}Zero2542]
  norm_num

""")
            continue
        z, depth = row["trace"][0], row["depth"]
        inp = p + "Input2542"
        text.append(f"""def {inp} : RatPair2542 :=
  {pair(z)}

theorem {p}Compute2542 : compactExp2542 {inp} {depth} = {out} := by
  cbv

theorem {p}Owner2542 : {unit} =
    Complex.exp ((2 : ℂ)^{depth} * embedPair2542 {inp}) := by
  have hx : |{pos}| < storedWidth ⟨{i}, by omega⟩ ^ 2 := by
    norm_num [{pos}, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [{pos}, storedWidth, nodeModulation2541, embedPair2542, {inp},
      Complex.mul_re, Complex.mul_im]

theorem {p}Error2542 :
    ‖{unit} - embedPair2542 {out}.1‖ ≤ ({out}.2 : ℝ) := by
  have hz : ‖embedPair2542 {inp}‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, {inp}]
  rw [{p}Owner2542]
  have h := compactExp_error2542 {inp} hz {depth}
  simpa only [{p}Compute2542] using h

theorem {p}Norm2542 : ‖{unit}‖ ≤ 1 := by
  rw [{p}Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, {inp}, Complex.mul_re, Complex.mul_im]

""")
    for suffix, typ, rhs in (("Value", "ℂ", lambda i:f"embedPair2542 {prefix}P{i:03d}Output2542.1"),
                             ("Error", "ℝ", lambda i:f"({prefix}P{i:03d}Output2542.2 : ℝ)")):
        text.append(f"noncomputable def {prefix}{suffix}2542 (i : Fin 30) : {typ} :=\n  match i.val with\n")
        text.extend(f"  | {i} => {rhs(i)}\n" for i in range(30))
        text.append("  | _ => 0\n\n")
    for suffix, goal, proofsuffix in (
        ("Exp_error", f"‖weightedUnitJet2539 0 ({real(sigma)}) nodeModulation2541 i {pos} - {prefix}Value2542 i‖ ≤ {prefix}Error2542 i", "Error"),
        ("Unit_norm", f"‖weightedUnitJet2539 0 ({real(sigma)}) nodeModulation2541 i {pos}‖ ≤ 1", "Norm")):
        text.append(f"theorem {prefix}{suffix}2542 (i : Fin 30) :\n    {goal} := by\n  fin_cases i\n")
        text.extend(f"  · simpa only [{prefix}Value2542, {prefix}Error2542] using {prefix}P{i:03d}{proofsuffix}2542\n" for i in range(30))
        text.append("\n")
    total = (Q(0), Q(0))
    charge = Q(0)
    for center, row in zip(centers, rows):
        total = add(total, mul(center, row["center"]))
        charge += sum(abs(v) for v in center)*row["error"]
    sq = sum(v*v for v in total)
    scale = 10**10
    numerator = isqrt(sq.numerator*scale**2//sq.denominator)+1
    norm_upper = Q(numerator, scale)
    assert norm_upper**2 >= sq and charge <= Q(1, 10**12)
    upper = norm_upper + Q(1,10**10)
    text.append(f"noncomputable def {prefix}SumValue2542 : ℂ := {complex_pair(total)}\n\n")
    text.append(f"noncomputable def {prefix}Upper2542 : ℝ := {real(upper)}\n\n")
    defs = ",\n      ".join(f"{prefix}P{i:03d}Output2542" for i in range(30))
    text.append(f"""theorem {prefix}Sum_eq2542 :
    (∑ i : Fin 30, baseCoefficientCenter2540 i * {prefix}Value2542 i) =
      {prefix}SumValue2542 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, {prefix}Value2542,
      {prefix}SumValue2542, embedPair2542, {defs}, Complex.mul_re, Complex.mul_im]

theorem {prefix}Sum_norm2542 :
    ‖∑ i : Fin 30, baseCoefficientCenter2540 i * {prefix}Value2542 i‖ ≤
      {real(norm_upper)} := by
  rw [{prefix}Sum_eq2542]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [{prefix}SumValue2542]

theorem {prefix}Evaluation_charge2542 :
    (∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
      |(baseCoefficientCenter2540 i).im|) * {prefix}Error2542 i) ≤ (1 : ℝ)/10^12 := by
  rw [sum30_chain2541]
  norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, {prefix}Error2542,
      {defs}]

""")
    old = (ROOT / "ConnesWeilRH/Dev/C1RouteANonzeroNode2541.lean").read_text()
    body = old[old.index("theorem signedJet_nonzero_le2541"):old.index("theorem production_grid_nonzero2541")]
    for a, b in (("nodeExp_error2541", f"{prefix}Exp_error2542"),
                 ("nodeUnit_norm2541", f"{prefix}Unit_norm2542"),
                 ("nodeSum_norm2541", f"{prefix}Sum_norm2542"),
                 ("nodeEvaluation_charge2541", f"{prefix}Evaluation_charge2542"),
                 ("nodePosition2541", pos), ("nodeValue2541", f"{prefix}Value2542"),
                 ("nodeError2541", f"{prefix}Error2542"), ("nodeUpper2541", f"{prefix}Upper2542"),
                 ("signedJet_nonzero_le2541", f"{prefix}Signed_le2542"),
                 ("weightedPhysical_nonzero_le2541", f"{prefix}Physical_le2542")):
        body = body.replace(a, b)
    text.append(body.replace("(1/2)", f"({real(sigma)})"))
    text.append(f"""theorem {prefix}Grid2542 :
    -stripRadius2303 + ({index} : ℝ)*(2*stripRadius2303/10240) = {pos} := by
  norm_num [stripRadius2303, {pos}]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.{prefix}Signed_le2542
#print axioms ConnesWeilRH.Dev.{prefix}Physical_le2542
""")
    formatted = []
    for line in "".join(text).splitlines():
        indent = len(line) - len(line.lstrip())
        formatted.extend(textwrap.wrap(line, width=98, subsequent_indent=" "*(indent+4),
                                       break_long_words=False, break_on_hyphens=False) or [""])
    return "\n".join(formatted)+"\n", dict(index=index, sign=sign, node=str(x), upper=str(upper),
                              charge=str(charge), max_depth=max(r["depth"] for r in rows),
                              active_families=sum(not r["exterior"] for r in rows))


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--index", type=int, choices=(5440,10239), default=5440)
    parser.add_argument("--sign", type=int, choices=(-1,1), default=1)
    args = parser.parse_args()
    source, info = render(args.index, args.sign)
    name = f"C1RouteAAdaptiveN{args.index:05d}{'Plus' if args.sign > 0 else 'Minus'}2542"
    (ROOT / f"ConnesWeilRH/Dev/{name}.lean").write_text(source, encoding="utf-8", newline="\n")
    print(json.dumps(info), flush=True)
