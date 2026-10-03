"""Replay the worst order-three endpoint component in cell 2700 at 160 bits."""
from fractions import Fraction as Q
import json
import textwrap

from generate_complex_exp_node_2541 import ROOT, CAPTURE, real
from generate_compact_replay_2542 import pair
from price_boundary_precision_2547 import precision_evaluate
from routea_exp_schedule_probe_2542 import R, STEP
from routea_derivative_pricing_2543 import multiplier


def render(*, grid_index=None, family_index=None, order=3, sigma=Q(1,2), paired=False):
    assert sigma in (Q(1,2), Q(-1,2))
    assert order in (2,3)
    candidates = []
    raw = json.loads(CAPTURE.read_text())["owner_capture"]["families_hex"]
    rows = json.loads((ROOT/"results/2338_exact_interpolation_repair.json").read_text())["coefficient_rows"]
    indices = (2700,2701) if grid_index is None else (Q(grid_index),)
    for index in indices:
        x = -R+index*STEP
        for i,(values,row) in enumerate(zip(raw,rows)):
            if family_index is not None and i != family_index:
                continue
            width,theta = (Q.from_float(float.fromhex(v)) for v in values)
            radius = width**2
            if abs(x) >= radius:
                continue
            factor = multiplier(order,radius,theta,sigma,x)
            mag = sum(abs((Q(row["ideal_base_coefficient"][p]["lower_exact"])+
                          Q(row["ideal_base_coefficient"][p]["upper_exact"]))/2) for p in ("real","imag"))
            error = precision_evaluate(radius,theta,x,sigma,100)[1]
            candidates.append((mag*sum(abs(v) for v in factor)*error,index,i,x,radius,theta,factor))
    charge,index,i,x,radius,theta,factor = max(candidates)
    center,error,depth = precision_evaluate(radius,theta,x,sigma,160)
    z = ((sigma*x-30/(1-(x/radius)**2))/2**depth,theta*x/2**depth)
    source = f"""import ConnesWeilRH.Dev.C1RouteACompactExp1602547
import ConnesWeilRH.Dev.C1RouteADerivativeMultiplier2543
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def boundaryPosition2547 : ℝ := {real(x)}

def boundaryInput2547 : RatPair2542 := {pair(z)}

def boundaryCenter2547 : RatPair2542 := {pair(center)}

def boundaryFactor2547 : RatPair2542 := {pair(factor)}

noncomputable def boundaryError2547 : ℝ := {real(error)}

theorem boundaryBaseError2547 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨{i}, by omega⟩ boundaryPosition2547 -
      embedPair2542 boundaryCenter2547‖ ≤ boundaryError2547 := by
  have hx : |boundaryPosition2547| < storedWidth ⟨{i}, by omega⟩ ^ 2 := by
    norm_num [boundaryPosition2547, storedWidth]
  have hz : ‖embedPair2542 boundaryInput2547‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, boundaryInput2547]
  have hc : (compactExp2547 boundaryInput2547 {depth}).1 = boundaryCenter2547 := by cbv
  have he : ((compactExp2547 boundaryInput2547 {depth}).2 : ℝ) = boundaryError2547 := by
    have hq : (compactExp2547 boundaryInput2547 {depth}).2 =
        {real(error).replace('ℝ','ℚ')} := by cbv
    rw [hq]
    norm_num [boundaryError2547]
  have h := compactExp_error2547 boundaryInput2547 hz {depth}
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨{i}, by omega⟩
      boundaryPosition2547 = Complex.exp ((2 : ℂ)^{depth} * embedPair2542 boundaryInput2547) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [boundaryPosition2547, storedWidth, nodeModulation2541,
      embedPair2542, boundaryInput2547, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem boundaryThirdError2547 :
    ‖weightedUnitJet2539 {order} (1/2) nodeModulation2541 ⟨{i}, by omega⟩ boundaryPosition2547 -
      embedPair2542 boundaryFactor2547 * embedPair2542 boundaryCenter2547‖ ≤
        (pairMagnitude2542 boundaryFactor2547 : ℝ) * boundaryError2547 := by
  have hx : |boundaryPosition2547| < storedWidth ⟨{i}, by omega⟩ ^ 2 := by
    norm_num [boundaryPosition2547, storedWidth]
  have hf : weightedMultiplier2543 {order} (1/2) (nodeModulation2541 ⟨{i}, by omega⟩)
      (storedWidth ⟨{i}, by omega⟩ ^ 2) boundaryPosition2547 = embedPair2542 boundaryFactor2547 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      boundaryPosition2547, storedWidth, nodeModulation2541, embedPair2542,
      boundaryFactor2547, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 {order} (by omega) (1/2)
    (nodeModulation2541 ⟨{i}, by omega⟩) (pow_pos (storedWidth_pos ⟨{i}, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv {order} _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ boundaryBaseError2547
    (embedPair_magnitude2542 boundaryFactor2547)

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.boundaryBaseError2547
#print axioms ConnesWeilRH.Dev.boundaryThirdError2547
"""
    if sigma == Q(-1,2):
        source = source.replace("(1/2)", "(-1/2)")
    if paired:
        start = source.index("  have hc :")
        end = source.index("  have h := compactExp_error2547", start)
        replacement = f"""  have hs : compactExp2547 boundaryInput2547 {depth} =
      (boundaryCenter2547, {real(error).replace('ℝ','ℚ')}) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 boundaryInput2547 {depth}).2 : ℝ) = boundaryError2547 := by
    rw [hs]
    norm_num [boundaryError2547]
"""
        source = source[:start] + replacement + source[end:]
    lines = []
    for line in source.splitlines():
        indent = len(line)-len(line.lstrip())
        lines.extend(textwrap.wrap(line,width=98,subsequent_indent=" "*(indent+4),
                                  break_long_words=False,break_on_hyphens=False) or [""])
    return "\n".join(lines)+"\n",dict(index=index,family=i,depth=depth,
                                         old_weighted_error_display=float(charge))


if __name__ == "__main__":
    source,info = render()
    (ROOT/"ConnesWeilRH/Dev/C1RouteABoundaryReplay2547.lean").write_text(source,encoding="utf-8",newline="\n")
    print("BOUNDARY_REPLAY_GENERATED",info,flush=True)
