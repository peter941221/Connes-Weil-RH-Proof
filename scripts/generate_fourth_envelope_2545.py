"""Exact rational payloads for the existing cell-5440 fourth envelope."""
import argparse
from fractions import Fraction as Q
from math import comb, isqrt
import json
import textwrap

from generate_complex_exp_node_2541 import ROOT, CAPTURE, real
from generate_compact_replay_2542 import pair
from routea_exp_schedule_probe_2542 import evaluate, R, STEP


def polynomial(k, t):
    rows = ((1,), (0,60), (60,0,3480,0,180),
            (0,10080,0,193680,0,31680,0,720),
            (10080,0,1085040,0,10189440,0,3575520,0,266400,0,3600))
    return sum(Q(c)*t**j for j,c in enumerate(rows[k]))


def render(count, *, cell_index=5440, indices=None, precision=100, sigma=Q(1,2)):
    assert precision in (100,160)
    assert sigma in (Q(1,2),Q(-1,2))
    a,b = -R+cell_index*STEP,-R+(cell_index+1)*STEP
    selected = list(range(count)) if indices is None else list(indices)
    families = json.loads(CAPTURE.read_text())["owner_capture"]["families_hex"]
    parts = ["""import ConnesWeilRH.Dev.C1RouteAFactoredCellEnvelope2545

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

"""]
    readings = []
    for i in selected:
        width,theta = (Q.from_float(float.fromhex(v)) for v in families[i])
        r = width**2
        near,far = min(abs(a),abs(b))/r,min(max(abs(a),abs(b)),r)/r
        assert a*b >= 0 and 0 <= near < 1 and near < far <= 1
        growth = max(sigma*a,sigma*b)
        exponent = growth-30/(1-near**2)
        # Reuse only the proved scalar exponential algorithm: its real
        # argument is the maximum signed endpoint growth minus bump decay.
        if precision == 160 or near == 0:
            from price_boundary_precision_2547 import precision_exponential
            center,error,depth = precision_exponential((exponent,Q(0)),precision)
            ev = dict(center=center,error=error,depth=depth,trace=((exponent/2**depth,Q(0)),))
        else:
            closest = near*r
            ev = evaluate(r,Q(0),closest,growth/closest)
        z,k = ev["trace"][0],ev["depth"]
        assert z == (exponent/2**k,0)
        exponential = sum(abs(v) for v in ev["center"])+ev["error"]
        sq = Q(1,4)+theta**2
        scale = 2**40
        frequency = Q(isqrt(sq.numerator*scale**2//sq.denominator)+1,scale)
        poly = sum(comb(4,j)*frequency**j*polynomial(4-j,far)*
                   (1-near**2)**(-2*(4-j))/r**(4-j) for j in range(5))
        raw = exponential*poly
        upper = Q(-((-raw.numerator*2**precision)//raw.denominator),2**precision)
        p = f"fourthP{i:03d}"
        parts.append(f"""def {p}Input2545 : RatPair2542 := {pair(z)}

def {p}Center2545 : RatPair2542 := {pair(ev['center'])}

noncomputable def {p}Error2545 : ℝ := {real(ev['error'])}

noncomputable def {p}ExpUpper2545 : ℝ := {real(exponential)}

noncomputable def {p}Frequency2545 : ℝ := {real(frequency)}

noncomputable def {p}Upper2545 : ℝ := {real(upper)}

noncomputable def {p}Exponent2545 : ℝ := {real(exponent)}

theorem {p}ExpBound2545 :
    Real.exp {p}Exponent2545 ≤ {p}ExpUpper2545 := by
  have hz : ‖embedPair2542 {p}Input2545‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, {p}Input2545]
  have hc : (compactExp2542 {p}Input2545 {k}).1 = {p}Center2545 := by cbv
  have he : ((compactExp2542 {p}Input2545 {k}).2 : ℝ) = {p}Error2545 := by
    have hq : (compactExp2542 {p}Input2545 {k}).2 =
        {real(ev['error']).replace('ℝ','ℚ')} := by cbv
    rw [hq]
    norm_num [{p}Error2545]
  have h := compactExp_error2542 {p}Input2545 hz {k}
  rw [hc, he] at h
  have ha : (2 : ℂ)^{k} * embedPair2542 {p}Input2545 =
      ({p}Exponent2545 : ℂ) := by
    apply Complex.ext <;> norm_num [embedPair2542, {p}Input2545, {p}Exponent2545,
      Complex.mul_re, Complex.mul_im]
  rw [ha] at h
  have ht := midpoint_triangle2543
    (Complex.exp ({p}Exponent2545 : ℂ)) (embedPair2542 {p}Center2545) 0
  simp only [sub_zero, Complex.norm_exp_ofReal] at ht
  apply (ht.trans (add_le_add h (embedPair_magnitude2542 {p}Center2545))).trans
  norm_num [{p}Error2545, {p}ExpUpper2545, pairMagnitude2542, {p}Center2545]

theorem {p}Bound2545 : fourthCellTerm2544 ⟨{i}, by omega⟩ ≤ {p}Upper2545 := by
  have hf : ‖weightedLambda2537 (1/2) (nodeModulation2541 ⟨{i}, by omega⟩)‖ ≤
      {p}Frequency2545 := by
    apply complex_norm_le_of_sq2541 _ _ (by norm_num [{p}Frequency2545])
    norm_num [weightedLambda2537, nodeModulation2541, {p}Frequency2545,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have h := weightedCell_upper2545 4 (1/2) (nodeModulation2541 ⟨{i}, by omega⟩)
    {real(r)} {real(near)} {real(far)} {real(a)} {real(b)}
    (by norm_num) (by norm_num) hf
    (by convert {p}ExpBound2545 using 1; norm_num [{p}Exponent2545])
  have hid : fourthCellTerm2544 ⟨{i}, by omega⟩ =
      weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 ⟨{i}, by omega⟩)
        {real(r)} {real(near)} {real(far)} {real(a)} {real(b)} := by
    norm_num [fourthCellTerm2544, cellNearAbs2538, endpointLeftPosition2544,
      endpointRightPosition2544, storedWidth]
  rw [hid]
  apply h.trans
  norm_num [cellPolynomial2545, bumpNumeratorAbsUpper2536, Finset.sum_range_succ, Nat.choose,
    {p}ExpUpper2545, {p}Frequency2545, {p}Upper2545]

""")
        readings.append(dict(index=i,exponential_upper=str(exponential),frequency=str(frequency),
                             upper=str(upper),upper_display=float(upper)))
    if selected == list(range(30)):
        parts.append("noncomputable def fourthUpper2545 (i : Fin 30) : ℝ :=\n  match i.val with\n")
        parts.extend(f"  | {i} => fourthP{i:03d}Upper2545\n" for i in range(30))
        parts.append("  | _ => 0\n\n")
        parts.append("theorem fourthBound2545 (i : Fin 30) :\n"
                     "    fourthCellTerm2544 i ≤ fourthUpper2545 i := by\n  fin_cases i\n")
        parts.extend(f"  · exact fourthP{i:03d}Bound2545\n" for i in range(30))
        parts.append("\n")
    parts.append("end ConnesWeilRH.Dev\n\n")
    parts.extend(f"#print axioms ConnesWeilRH.Dev.fourthP{i:03d}Bound2545\n" for i in selected)
    if selected == list(range(30)):
        parts.append("#print axioms ConnesWeilRH.Dev.fourthBound2545\n")
    lines = []
    output = "".join(parts)
    if sigma < 0:
        output = output.replace("(1/2)","(-1/2)")
    if precision == 160:
        output = output.replace("compactExp2542","compactExp2547").replace("compactExp_error2542","compactExp_error2547")
    for line in output.splitlines():
        indent = len(line)-len(line.lstrip())
        lines.extend(textwrap.wrap(line,width=98,subsequent_indent=" "*(indent+4),
                                  break_long_words=False,break_on_hyphens=False) or [""])
    return "\n".join(lines)+"\n",readings


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--count",type=int,default=30,choices=range(1,31))
    args = parser.parse_args()
    source,rows = render(args.count)
    (ROOT/"ConnesWeilRH/Dev/C1RouteAFourthEnvelope2545.lean").write_text(source,encoding="utf-8",newline="\n")
    print("FOURTH_ENVELOPE_GENERATED",len(rows),"max",max(r["upper_display"] for r in rows),flush=True)
